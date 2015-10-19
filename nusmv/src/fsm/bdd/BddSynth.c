#include <math.h>

#include "enc/encInt.h"
#include "enc/bdd/BddEnc.h"
#include "bddInt.h"
#include "BddFsm.h"
#include "BddSynth.h"
#include "FairnessList.h"
#include "dd/dd.h"
#include "enc/bdd/BddEnc.h"
#include "enc/bdd/BddEnc_private.h"

#include "parser/symbols.h"
#include "fsm/sexp/BoolSexpFsm.h"
#include "compile/compile.h"
#include "compile/symb_table/SymbTable.h"
#include "enc/enc.h"
#include "utils/utils.h"
#include "utils/utils_io.h"
#include "utils/error.h"
#include "utils/assoc.h"
#include "trans/bdd/ClusterList.h"
#include "cudd.h"

typedef struct BddSynth_TAG
{
  DdManager * dd;
  BddEnc_ptr enc;
  BddFsm_ptr fsm;

  NodeList_ptr all_vars;
  NodeList_ptr latches;
  NodeList_ptr cinputs;
  NodeList_ptr uinputs;
  NodeList_ptr outputs;

  bdd_ptr init;
  bdd_ptr error;
  bdd_ptr cinput_cube;
  bdd_ptr uinput_cube;
  bdd_ptr latch_cube;

  /** An array of BDDs indexed by
   * variables indices. For each variable of index i,
   * trans[i] contains the BDD describing when the next
   * state variable i is set to true. */
  bdd_ptr * trans;
}BddSynth;

static void bdd_synth_init ARGS((BddSynth_ptr self, BddFsm_ptr fsm));
static bdd_ptr bdd_synth_upre ARGS((BddSynth_ptr self, bdd_ptr states));
static bdd_ptr bdd_synth_upre_trans ARGS((BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans));
static bdd_ptr bdd_synth_cpre ARGS((BddSynth_ptr self, bdd_ptr states));
static bdd_ptr bdd_synth_cpre_trans ARGS((BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans));

static bdd_ptr bdd_synth_upre_star ARGS((BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe));
static bdd_ptr bdd_synth_cpre_star ARGS((BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe));
static boolean bdd_synth_forward_backward_synth ARGS((BddSynth_ptr self, bdd_ptr * win));

void dump_tmp_and_wait(BddSynth_ptr self, bdd_ptr nextFront){
    char * labels = "Upre";
    FILE * outfile = fopen("/tmp/a.dot", "w");
    if (!outfile){
      return;
    }
    AddArray_ptr ar = AddArray_create(1);
    AddArray_set_n(ar,0,bdd_to_add(self->dd, nextFront));
    BddEnc_dump_addarray_dot(self->enc, ar, (const char **)&labels, outfile);
    fclose(outfile);
    while(getchar() != 'c');
}

void bdd_synth_init(BddSynth_ptr self, BddFsm_ptr fsm){
  self->enc = BddFsm_get_bdd_encoding(fsm);
  self->dd = BddEnc_get_dd_manager(self->enc);
  self->fsm = fsm;
  self->latches = NodeList_create();
  self->uinputs = NodeList_create();
  self->cinputs = NodeList_create();
  self->outputs = NodeList_create();
  self->all_vars = NodeList_create();
  self->latch_cube = bdd_true(self->dd);
  self->uinput_cube = bdd_true(self->dd);
  self->cinput_cube = bdd_true(self->dd);
  self->error = NULL;
  BddVarSet_ptr state_vars_bdd = BddEnc_get_state_vars_cube(self->enc);
  BddEnc_synth_get_game(self->enc, state_vars_bdd, 
      &self->all_vars,
      &self->latches, &self->latch_cube, 
      &self->uinputs, &self->uinput_cube, 
      &self->cinputs, &self->cinput_cube, 
      &self->outputs, &self->error);
  bdd_free(self->dd, state_vars_bdd);
  
  ListIter_ptr iter = NULL;
  ListIter_ptr trans_iter = NULL;

  // Prepare initial state
  self->init = bdd_true(self->dd);
  iter = NodeList_get_first_iter(self->latches);
  NODE_LIST_FOREACH(self->latches,iter){
    node_ptr var = NodeList_get_elem_at(self->latches,iter);
    bdd_ptr varbdd = BddEnc_expr_to_bdd(self->enc, var, Nil);
    bdd_and_accumulate(self->dd, &self->init, bdd_not(self->dd, varbdd));
    bdd_free(self->dd, varbdd);
  }

  // Create the list of primed latches
  NodeList_ptr platch_bdds = NodeList_create();
  iter = NodeList_get_first_iter(self->latches);
  NODE_LIST_FOREACH(self->latches,iter){
    node_ptr var = NodeList_get_elem_at(self->latches,iter);
    bdd_ptr varbdd = BddEnc_expr_to_bdd(self->enc, var, Nil);
    bdd_ptr pvarbdd = BddEnc_state_var_to_next_state_var(self->enc, varbdd);
    NodeList_append(platch_bdds, (node_ptr) pvarbdd);
    bdd_free(self->dd, varbdd);
  }

  // List of pairs of primed latch and trans. function
  NodeList_ptr trans_rels = BddFsm_get_trans_expr(self->fsm);
  NodeList_ptr trans_funcs = NodeList_create();
  iter = NodeList_get_first_iter(platch_bdds);
  NODE_LIST_FOREACH(platch_bdds, iter){
    bdd_ptr pvar = (bdd_ptr) NodeList_get_elem_at(platch_bdds, iter);
    bdd_ptr trans = NULL;
    trans_iter = NodeList_get_first_iter(trans_rels);
    NODE_LIST_FOREACH(trans_rels, trans_iter){
      bdd_ptr t = (bdd_ptr)NodeList_get_elem_at(trans_rels, trans_iter);
      bdd_ptr tFunc = bdd_and_abstract(self->dd, pvar, t, pvar);
      if (tFunc != t){
        if (trans != NULL){
          fprintf(stderr, "[ERR] Two transition relations depend on the same next-state variable!\n");
          fprintf(stderr, "[ERR] Are the two funcs the same? %d\n", 
              NodeList_count_elem(trans_funcs, (node_ptr)trans));
          exit(-1);
        }
        // Make the error state a sink state
        if (t == self->error){
           bdd_or_accumulate(self->dd, &tFunc, self->error);
        }
        trans = tFunc;
        NodeList_append(trans_funcs, (node_ptr) trans);
      } else {
        bdd_free(self->dd, tFunc);
      }
    }
  }

  // Prepare compose vector
  // for any BDD B(L'), B.vector_compose(X)
  // gives the predecessors A(L,X_u,X_c) of B
	int nvars = Cudd_ReadSize(self->dd);
	DdNode **X = ALLOC(DdNode *,nvars);
	for (int i = 0; i < nvars; i++) {
		X[i] = NULL;
	}
	ListIter_ptr v = NodeList_get_first_iter(platch_bdds);
	ListIter_ptr t = NodeList_get_first_iter(trans_funcs);
	bdd_ptr v_elm, t_elm;
	unsigned int vindex = 0;
	for(; !ListIter_is_end(v) && !ListIter_is_end(t); 
				v = ListIter_get_next(v),
				t = ListIter_get_next(t)){
		v_elm = (bdd_ptr)NodeList_get_elem_at(platch_bdds, v);
		t_elm = (bdd_ptr)NodeList_get_elem_at(trans_funcs, t);
		vindex = Cudd_NodeReadIndex(v_elm);
		assert(vindex >= 0 && vindex < nvars);
		// Just to check if the trans_funcs are well defined
		assert(X[vindex] == NULL);
		X[vindex] = t_elm;
	}
	for (int i = 0; i < nvars; i++) {
    if (X[i] == NULL){
      X[i] = Cudd_bddIthVar(self->dd, i);
    }
	}
  self->trans = X;
}

BddSynth_ptr BddSynth_create(BddFsm_ptr fsm){
  BddSynth_ptr ret = ALLOC(BddSynth, 1);
  BDD_SYNTH_CHECK_INSTANCE(ret);
  bdd_synth_init(ret, fsm);
  return ret;
}

void BddSynth_destroy(BddSynth_ptr self){
  NodeList_destroy(self->latches);
  NodeList_destroy(self->cinputs);
  NodeList_destroy(self->uinputs);
  NodeList_destroy(self->outputs);
  NodeList_destroy(self->all_vars);
  bdd_free(self->dd, self->latch_cube);
  bdd_free(self->dd, self->cinput_cube);
  bdd_free(self->dd, self->uinput_cube);
  bdd_free(self->dd, self->error);
  bdd_free(self->dd, self->init);
  free(self);
}

static bdd_ptr bdd_synth_cpre_trans(BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans){
  bdd_ptr * local_trans = trans;
#ifdef RESTRICT_IN_CPRE
  bdd_ptr notstates = bdd_not(self->dd, states);
  int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * Y = ALLOC(bdd_ptr, nvar);
  int i;
  for (i = 0; i < nvar; i++){
    Y[i] = bdd_restrict(self->dd, trans[i], notstates);
  }
  local_trans = Y;
  bdd_free(self->dd, notstates);
#endif
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, local_trans);
  bdd_ptr pre2 = bdd_forsome(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forall(self->dd, pre2, self->uinput_cube);
  bdd_free(self->dd, pstates);
  bdd_free(self->dd, pre2);
  bdd_free(self->dd, pre1);
#ifdef RESTRICT_IN_CPRE
  for (i = 0; i < nvar; i++){
    bdd_free(self->dd, Y[i]);
  }
  free(Y);
#endif
  return pre3;
}


/** Upre computation with custom transition relation vector */
static bdd_ptr bdd_synth_upre_trans(BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans){
	// Further restrict the transition relation to ~states(L)
  bdd_ptr notstates = bdd_not(self->dd, states);
  int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * Y = ALLOC(bdd_ptr, nvar);
  for (int i = 0; i < nvar; i++){
    Y[i] = bdd_restrict(self->dd, trans[i], notstates);
  }
  bdd_free(self->dd, notstates);
	//
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, Y);
  bdd_ptr pre2 = bdd_forall(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forsome(self->dd, pre2, self->uinput_cube);
	// Clean up
  bdd_free(self->dd,pre2);
  bdd_free(self->dd,pre1);
  bdd_free(self->dd,pstates);
  for (int i = 0; i < nvar; i++){
    bdd_free(self->dd, Y[i]);
  }
  free(Y);
  return pre3;
}

static bdd_ptr bdd_synth_upre(BddSynth_ptr self, bdd_ptr states){
	return bdd_synth_upre_trans(self, states, self->trans);
}

static bdd_ptr bdd_synth_cpre(BddSynth_ptr self, bdd_ptr states){
	return bdd_synth_cpre_trans(self, states, self->trans);
}

/**
 * Compute the least fixpoint \mu X. ( universe /\ ( start \/  UPRE(X) ) )
 */ 
static bdd_ptr bdd_synth_upre_star(BddSynth_ptr self, bdd_ptr start, bdd_ptr universe){
	int n = Cudd_ReadSize(self->dd);
	int cnt = 1;
	bdd_ptr * restricted_trans = ALLOC(bdd_ptr, n);
	// Restrict the transition relation to (universe /\ ~start)(L)
	bdd_ptr not_start = bdd_not(self->dd, start);
	bdd_ptr universe_not_start = bdd_and(self->dd, not_start, universe);
	bdd_free(self->dd, not_start);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_restrict(self->dd, self->trans[i], universe_not_start);
	}
	bdd_free(self->dd, universe_not_start);
	//
	bdd_ptr iterate = bdd_and(self->dd, universe, start);
	bdd_ptr prev = NULL;
	while( iterate != prev ){
		printf("\tUpre iteration %d\n", cnt++);
		if (prev) bdd_free(self->dd, prev);
		prev = bdd_dup(iterate);
		bdd_ptr next = bdd_synth_upre_trans(self, prev, restricted_trans);
		bdd_or_accumulate(self->dd, &iterate, next);
		bdd_and_accumulate(self->dd, &iterate, universe);
		bdd_free(self->dd, next);
	}
	bdd_free(self->dd, prev);
	for (int i = 0; i < n ; i++){
		bdd_free(self->dd, restricted_trans[i]);
	}
	free(restricted_trans);
	return iterate;
}


void print_trans_size_cstm(BddSynth_ptr self, bdd_ptr * trans){
  int n = Cudd_ReadSize(self->dd);
  int total = 0;
  for(int i = 0; i < n; i++){
    total += Cudd_DagSize(trans[i]);
  }
  printf("Trans rel total size: %d\n", total);
}
void print_trans_size(BddSynth_ptr self){
  int n = Cudd_ReadSize(self->dd);
  int total = 0;
  for(int i = 0; i < n; i++){
    total += Cudd_DagSize(self->trans[i]);
  }
  printf("Trans rel total size: %d\n", total);
}


/**
 * Check if (a /\ universe) != (b /\ universe)
 */
static boolean check_different_inside(BddSynth_ptr self, bdd_ptr a, bdd_ptr b, bdd_ptr universe){
	
}

/**
 * Compute the greatest fixpoint \nu X. ( universe /\  CPRE(X) )
 */ 
static bdd_ptr bdd_synth_cpre_star(BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe){
	int n = Cudd_ReadSize(self->dd);
	int cnt = 1;
  bdd_ptr * restricted_trans = self->trans;
  /*
	// Restrict the transition relation to universe(L)
	bdd_ptr * restricted_trans = ALLOC(bdd_ptr, n);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_restrict(self->dd, self->trans[i], universe);
  }	 
  print_trans_size_cstm(self, restricted_trans);
	*/
	bdd_ptr notlosing = bdd_not(self->dd, losing);
	//bdd_ptr iterate = bdd_and(self->dd,universe, notlosing);
	bdd_ptr iterate = bdd_restrict(self->dd, notlosing, universe);
	bdd_ptr prev = NULL;
	while( iterate != prev ){
		printf("\tCpre iteration %d\n iterate size: %d\n", cnt++, Cudd_DagSize(iterate));
		printf("\tCpre iteration %d (Current iterate has dag size %d)\n", cnt++, Cudd_DagSize(iterate));
		if (prev) bdd_free(self->dd, prev);
		prev = bdd_dup(iterate);
		bdd_free(self->dd, iterate);
		iterate = bdd_synth_cpre_trans(self, prev, restricted_trans);
		bdd_and_accumulate(self->dd, &iterate, prev);

		/* VERSION 1 */
		bdd_ptr tmp = bdd_restrict(self->dd, iterate, universe);
		bdd_free(self->dd, iterate);
		iterate = tmp;
		/*
		/* VERSION 2*/
    bdd_and_accumulate(self->dd, &iterate, universe);
    //bdd_and_accumulate(self->dd, &iterate, universe);
    /*
    bdd_ptr tmp = Cudd_bddConstrain(self->dd, iterate, universe);
    bdd_free(self->dd, iterate);
    iterate = tmp;
    */
		*/
	}
	bdd_free(self->dd, prev);
	bdd_free(self->dd, notlosing);
	for (int i = 0; i < n ; i++){
		bdd_free(self->dd, restricted_trans[i]);
	}
	free(restricted_trans);
	return iterate;
}
/*
static boolean bdd_synth_forward_backward_synth(BddSynth_ptr self, bdd_ptr * win){
	boolean realizable = true;
	bdd_ptr losing = bdd_dup(self->error);
	bdd_ptr front = bdd_dup(self->init);
	bdd_ptr reached = bdd_false(self->dd);
	int cnt = 1;
	while ( bdd_isnot_false(self->dd, front) ){
		printf("Forward image iteration %d\n", cnt++);
		bdd_or_accumulate(self->dd, &reached, front);

		// Is there a counter-strategy staying inside reached?
		// Recompute UPRE
		bdd_ptr U_star = bdd_synth_upre_star(self, losing, reached);
		if ( bdd_included(self->dd, self->init, U_star) ){
			bdd_free(self->dd, U_star);
			realizable = false;
			break;
		}
		bdd_or_accumulate(self->dd, &losing, U_star);
		bdd_free(self->dd, U_star);

		// Is there a winning strategy staying inside reached?
		if (!bdd_included(self->dd, front, losing)){
			*win = bdd_synth_cpre_star(self, losing, reached);
			if ( bdd_included(self->dd, self->init, *win) ){
				break;
			}
		}

		// Get the image of front \ losing (projected to L)
    bdd_ptr notlosing = bdd_not(self->dd, losing);
		bdd_and_accumulate(self->dd, &front, notlosing);
		bdd_free(self->dd, notlosing);
		bdd_ptr tmp = BddFsm_get_forward_image(self->fsm, front);
		bdd_free(self->dd, front);
    bdd_ptr tmp1 = bdd_forsome(self->dd, tmp, self->cinput_cube);
    front = bdd_forsome(self->dd, tmp1, self->uinput_cube);
    bdd_free(self->dd, tmp);
    bdd_free(self->dd, tmp1);
    // Extract the new frontier
    bdd_ptr notreached = bdd_not(self->dd, reached);
    bdd_and_accumulate(self->dd, &front, notreached);
    bdd_free(self->dd, notreached);
	}
	return realizable;
}
*/


/**
 * TODO
 * 1) Check why UPRE is slow for amba5c5y.smv
 *    Does the size of trans rel grow?
 *    Is reached too large? So that each iterate is much larger when intersected
 *    with reached?
 * 2) Check constrain. Can't we use good properties of this here?
 */
static boolean bdd_synth_forward_backward_synth(BddSynth_ptr self, bdd_ptr * win){
	boolean realizable = true;
	bdd_ptr losing = bdd_dup(self->error); // under-approximation
	bdd_ptr winning = bdd_false(self->dd); // under-approximation
	bdd_ptr reached = bdd_false(self->dd);
	int cnt = 1;
	// how many reachability layers we explore at each step
	int expand_steps = 4; 
	boolean completed = false;
	boolean prev_completed = false;
	int diameter = 0;
	int new_diameter;
	BddStates* layers;
	bdd_ptr front = bdd_dup(self->init);
	bdd_ptr inputs = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);
	do {
		printf("Forward image iteration %d\n", cnt++);
		completed = prev_completed;

		// Is there a counter-strategy staying inside reached?
		// Recompute UPRE
		bdd_ptr U_star = bdd_synth_upre_star(self, losing, reached);
		if ( bdd_included(self->dd, self->init, U_star) ){
			bdd_free(self->dd, U_star);
			realizable = false;
			break;
		}
		bdd_or_accumulate(self->dd, &losing, U_star);
		bdd_free(self->dd, U_star);

		// Is there a winning strategy staying inside reached?
		if (!bdd_included(self->dd, front, losing)){
			*win = bdd_synth_cpre_star(self, losing, reached);
			if ( bdd_included(self->dd, self->init, *win) ){
				break;
			}
		}

		BddFsm_expand_cached_reachable_states(self->fsm, expand_steps, -1);
		prev_completed = BddFsm_get_cached_reachable_states(self->fsm, &layers, &new_diameter);

		// front is the newly added reachable states
		bdd_free(self->dd, front);
		front = bdd_false(self->dd);
		for (int i = diameter; i < new_diameter; i++){
			bdd_or_accumulate(self->dd, &front, layers[i]);
		}
		bdd_ptr tmp = bdd_forsome(self->dd, front, inputs);
		bdd_free(self->dd, front);
		front = tmp;

		// Update diameter
		diameter = new_diameter;

		// Compute the union of reached states
		bdd_or_accumulate(self->dd, &reached, front);
	}while(!completed);

	bdd_free(self->dd, inputs);
	return realizable;
}

/**
 * Just backwards computation preceded by a fwd reachable states computation
 */
static boolean bdd_synth_backward_synth(BddSynth_ptr self, bdd_ptr * win){
  boolean use_upre = false;
  boolean ret = true;
  if (use_upre){
    *win = bdd_dup(self->error);
  } else {
    *win = bdd_not(self->dd, self->error);
  }
  bdd_ptr prev = NULL;
	bdd_ptr tmp1, tmp2;
  int count = 0;
  while( ret && prev != *win ){
    printf("Bwd Iteration: %d\n", ++count);
    if (prev != NULL) bdd_free(self->dd, prev);
    prev = *win;
		tmp1 = *win;
    if (use_upre){
      *win = bdd_synth_upre(self, prev);
			tmp2 = *win;
      bdd_or_accumulate(self->dd, win, prev);
    } else {
      *win = bdd_synth_cpre(self, prev);
      bdd_and_accumulate(self->dd, win, prev);
    }
    // dump_tmp_and_wait(self, *win);
    // Check init & *win != empty
    bdd_ptr check = bdd_and(self->dd, self->init, *win);
    if (use_upre && bdd_isnot_false(self->dd, check)){
				ret = false;
    }
		if (!use_upre && bdd_is_false(self->dd, check)){
      ret = false;
    }
    bdd_free(self->dd, check);
  }
  return ret;
}

static boolean bdd_synth_backward_synth_reach(BddSynth_ptr self, bdd_ptr * win){
  boolean ret = true;
	// Compute first reachable states
	 // This is the local version where we clean up the intermediary layers
	/*
	bdd_ptr reachables = bdd_false(self->dd);
	bdd_ptr front = bdd_dup(self->init);
	int reach_cnt = 1;
	while( bdd_isnot_false(self->dd, front) ){
		reach_cnt++;
		bdd_or_accumulate(self->dd, &reachables, front);
		bdd_ptr newFront = BddFsm_get_forward_image(self->fsm, front);
		bdd_free(self->dd, front);
		bdd_and_accumulate(self->dd, &newFront, bdd_not(self->dd,reachables));
		front = newFront;
	}
	printf("Reachable states computed. Diameter: %d\n", reach_cnt);
	*/
	// This is the NuSMV's version where it keeps the layers referenced
	int diameter;
  BddStates* layers;

  // Debug log
  print_trans_size(self);
  BddFsm_expand_cached_reachable_states(self->fsm, -1, -1);
  // Debug log
  print_trans_size(self);
  boolean completed = BddFsm_get_cached_reachable_states(self->fsm, &layers, &diameter);
	bdd_ptr reachables = bdd_false(self->dd);
	for(int i = 0; i < diameter; i++){
		bdd_or_accumulate(self->dd, &reachables, layers[i]);
	}
	bdd_ptr tmp = bdd_forsome(self->dd, reachables, self->cinput_cube);
	bdd_ptr tmp1 = bdd_forsome(self->dd, tmp, self->uinput_cube);
	bdd_free(self->dd, reachables);
	bdd_free(self->dd, tmp);
	reachables = tmp1;
	printf("Reachable states computed. Diameter: %d\n", diameter);
	//
	*win = bdd_synth_cpre_star(self, self->error, reachables);
	bdd_and_accumulate(self->dd, win, self->init);
	return bdd_isnot_false(self->dd, *win);
}

EXTERN boolean BddSynth_solve(const BddSynth_ptr self, BddSynth_dir mode, bdd_ptr * win){
  boolean ret;
  switch(mode){
		case BDD_SYNTH_DIR_BWD:
			printf("Backward algorithm\n");
			*win = bdd_synth_cpre_star(self, self->error, bdd_true(self->dd));
			bdd_and_accumulate(self->dd, win, self->init);
			ret = bdd_isnot_false(self->dd, *win);
			break;
		case BDD_SYNTH_DIR_BWD_W_REACH:
			printf("Backward algorithm with forward reach states reduction\n");
			ret = bdd_synth_backward_synth_reach(self, win);
			break;
		case BDD_SYNTH_DIR_FWD:
			printf("Forward algorithm\n");
			ret = bdd_synth_forward_backward_synth(self, win);
			break;
		default:
			ret = false;
	}
	return ret;
}
