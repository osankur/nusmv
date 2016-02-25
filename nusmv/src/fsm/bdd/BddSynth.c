/*
 * TODO FIXME Reference count error on runf.sh cycle_sched_3_4_1.smv
 * 						Check other algorithms on all benchmarks
 *
	THINGS TO DO
	1) Simplify the simpler backwards algorithm into one call to upre_star
	2) Parameterize all basic cpre and upre calls to use_restrict, where we restrict
	to an over-approximation of (not start)
	3) Clean up unnecessary functions
 */

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
static bdd_ptr bdd_synth_upre ARGS((BddSynth_ptr self, bdd_ptr states, boolean use_restrict));
static bdd_ptr bdd_synth_upre_trans ARGS((BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans, boolean use_restrict));
static bdd_ptr bdd_synth_cpre ARGS((BddSynth_ptr self, bdd_ptr states, boolean use_restrict));
static bdd_ptr bdd_synth_cpre_trans ARGS((BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans, boolean use_restrict));

static bdd_ptr bdd_synth_upre_star ARGS((BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe, boolean early_exit));
static bdd_ptr bdd_synth_cpre_star ARGS((BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe, boolean early_exit));
static boolean bdd_synth_forward_backward_synth ARGS((BddSynth_ptr self, bdd_ptr * win));
static bdd_ptr bdd_synth_over_approximate ARGS((BddSynth_ptr self, bdd_ptr f, int threshold));

static bdd_ptr bdd_synth_over_approximate(BddSynth_ptr self, bdd_ptr f, int threshold){
	int numVars = (Cudd_ReadSize(self->dd) <= 1022)? Cudd_ReadSize(self->dd) : 1022;
	return bdd_over_approx(self->dd, f, numVars, threshold, 1, 1);
}

static void print_trans_size_cstm(BddSynth_ptr self, bdd_ptr * trans){
  int n = Cudd_ReadSize(self->dd);
  int total = 0;
  for(int i = 0; i < n; i++){
    total += Cudd_DagSize(trans[i]);
  }
  printf("Trans rel total size: %d\n", total);
}
static void print_trans_size(BddSynth_ptr self){
  int n = Cudd_ReadSize(self->dd);
  int total = 0;
  for(int i = 0; i < n; i++){
    total += Cudd_DagSize(self->trans[i]);
  }
  printf("Trans rel total size: %d\n", total);
}


static void dump_tmp_and_wait(BddSynth_ptr self, bdd_ptr nextFront){
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

static bdd_ptr bdd_synth_cpre_trans(BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans, boolean use_restrict)
{
	int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * local_trans = trans;
	/*
	bdd_ptr * Y = NULL;
	if (use_restrict){
		bdd_ptr notstates = bdd_not(self->dd, states);
		Y = ALLOC(bdd_ptr, nvar);
		bdd_ptr tmp = NULL;
		int i;
		for (i = 0; i < nvar; i++){
			Y[i] = bdd_safe_restrict(self->dd, trans[i], notstates);
		}
		local_trans = Y;
		bdd_free(self->dd, notstates);
	}
	*/
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, local_trans);
  bdd_ptr pre2 = bdd_forsome(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forall(self->dd, pre2, self->uinput_cube);
  bdd_free(self->dd, pstates);
  bdd_free(self->dd, pre2);
  bdd_free(self->dd, pre1);
	/*
	if (use_restrict){
		for (int i = 0; i < nvar; i++){
			bdd_free(self->dd, Y[i]);
		}
		free(Y);
	}
	*/
  return pre3;
}


/** Upre computation with custom transition relation vector */
static bdd_ptr bdd_synth_upre_trans(BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans, boolean use_restrict){
	// Further restrict the transition relation to ~states(L)
	bdd_ptr * Y = self->trans;
	/*
  bdd_ptr notstates = bdd_not(self->dd, states);
  int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * Y = ALLOC(bdd_ptr, nvar);
  for (int i = 0; i < nvar; i++){
    Y[i] = bdd_safe_restrict(self->dd, trans[i], notstates);
  }
  bdd_free(self->dd, notstates);
	*/
	//
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, Y);
  bdd_ptr pre2 = bdd_forall(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forsome(self->dd, pre2, self->uinput_cube);
	// Clean up
  bdd_free(self->dd,pre2);
  bdd_free(self->dd,pre1);
  bdd_free(self->dd,pstates);
	/*
  for (int i = 0; i < nvar; i++){
    bdd_free(self->dd, Y[i]);
  }
  free(Y);
	*/
  return pre3;
}

static bdd_ptr bdd_synth_upre(BddSynth_ptr self, bdd_ptr states, boolean use_restrict){
	return bdd_synth_upre_trans(self, states, self->trans, use_restrict);
}

static bdd_ptr bdd_synth_cpre(BddSynth_ptr self, bdd_ptr states, boolean use_restrict){
	return bdd_synth_cpre_trans(self, states, self->trans, use_restrict);
}

/**
 * Compute the least fixpoint \mu X. ( universe /\ ( start \/  UPRE(X) ) )
 * If early_exit is set to true, then stop the iteration early and return
 * current iterate which is not the greatest fixpoint.
 */ 
static bdd_ptr bdd_synth_upre_star(BddSynth_ptr self, bdd_ptr start, bdd_ptr universe, boolean early_exit){
	int n = Cudd_ReadSize(self->dd);
	int cnt = 1;
	
	// Restrict the transition relation to (universe /\ ~start)(L)
	bdd_ptr * restricted_trans = ALLOC(bdd_ptr, n);
	bdd_ptr not_start = bdd_not(self->dd, start);
	bdd_ptr universe_not_start = bdd_and(self->dd, not_start, universe);
	bdd_free(self->dd, not_start);
	bdd_ptr appr_universe_not_start = bdd_synth_over_approximate(self, universe_not_start, 1000);
	bdd_free(self->dd, universe_not_start);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_safe_restrict(self->dd, self->trans[i], appr_universe_not_start);
	}
	bdd_free(self->dd, appr_universe_not_start);
  print_trans_size_cstm(self, restricted_trans);
	//
	printf("\tStarting UPRE fixpoint\n");
	bdd_ptr iterate = bdd_and(self->dd, universe, start);
	bdd_ptr prev = NULL;
	while( iterate != prev ){
		printf("\tUpre iteration %d (iterate size: %d)\n", cnt++, Cudd_DagSize(iterate));
		if (prev) bdd_free(self->dd, prev);
		prev = bdd_dup(iterate);
		bdd_ptr next = bdd_synth_upre_trans(self, prev, restricted_trans, true);
		bdd_or_accumulate(self->dd, &iterate, next);
		bdd_free(self->dd, next);
		bdd_and_accumulate(self->dd, &iterate, universe);
		if (early_exit && bdd_included(self->dd, self->init, iterate) ){
			break;
		}
	}
	bdd_free(self->dd, prev);

	// Free restricted trans rels
	for (int i = 0; i < n ; i++){
		bdd_free(self->dd, restricted_trans[i]);
	}
	free(restricted_trans);
	return iterate;
}



/**
 * Compute the greatest fixpoint \nu X. ( universe /\  CPRE(X) )
 */ 
static bdd_ptr bdd_synth_cpre_star(BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe, boolean early_exit){
	int n = Cudd_ReadSize(self->dd);
	int cnt = 1;
	bdd_ptr notlosing = bdd_not(self->dd, losing);

	// Restrict the transition relation to (an overapprox of) notlosing & universe(L)
	bdd_ptr * restricted_trans = ALLOC(bdd_ptr, n);
	bdd_and_accumulate(self->dd, &notlosing, universe);
	bdd_ptr appr_notlosing_and_universe = bdd_synth_over_approximate(self, notlosing, 1000);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_safe_restrict(self->dd, self->trans[i], appr_notlosing_and_universe);
  }	 
	bdd_free(self->dd, appr_notlosing_and_universe);
  print_trans_size_cstm(self, restricted_trans);

	bdd_ptr iterate = bdd_and(self->dd,universe, notlosing);
	bdd_ptr prev = NULL;
	printf("\tStarting CPRE fixpoint\n");
	while( iterate != prev ){
		printf("\tCpre iteration %d (iterate size: %d)\n", cnt++, Cudd_DagSize(iterate));
		if (prev) bdd_free(self->dd, prev);
		prev = iterate;
		iterate = bdd_synth_cpre_trans(self, prev, restricted_trans, true);
		if ( !bdd_included(self->dd, self->init, iterate) ){
			break;
		}
		bdd_and_accumulate(self->dd, &iterate, prev);
    bdd_and_accumulate(self->dd, &iterate, universe);
	}
	bdd_free(self->dd, prev);
	bdd_free(self->dd, notlosing);

	for (int i = 0; i < n ; i++){
		bdd_free(self->dd, restricted_trans[i]);
	}
	free(restricted_trans);

	return iterate;
}


/**
 * TODO
 * 1) Check why UPRE is slow for amba5c5y.smv
 *    Does the size of trans rel grow?
 *    Is reached too large? So that each iterate is much larger when intersected
 *    with reached?
 * 2) Check constrain. Can't we use good properties of this here?

runf does 1m16s on this
/home/sankur/work/ulb/syntcomp/bench-syntcomp14/smv/genbuf11f10unrealn.smv

against >5m for run
 */
static boolean bdd_synth_forward_backward_synth(BddSynth_ptr self, bdd_ptr * win){
	boolean realizable = true;
	bdd_ptr losing = bdd_dup(self->error); // under-approximation
	bdd_ptr reached = bdd_false(self->dd);
	bdd_ptr universe = reached; // an over-approx. of reached
	int cnt = 1;
	// how many reachability layers we explore at each step
	int expand_steps = 4; 
	boolean completed = false;
	boolean prev_completed = false;
	int diameter = 0;
	int new_diameter;
	BddStates* layers;
	// bdd_ptr front = bdd_dup(self->init);
	bdd_ptr inputs = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);
	do {
		printf("Forward image iteration %d (Diameter: %d, Reached size: %d) (Universe size: %d)\n", cnt++, diameter, Cudd_DagSize(reached), Cudd_DagSize(universe));
		completed = prev_completed;

		// Is there a counter-strategy staying inside reached?
		bdd_ptr U_star = bdd_synth_upre_star(self, losing, universe, true);
		if ( bdd_included(self->dd, self->init, U_star) ){
			bdd_free(self->dd, U_star);
			realizable = false;
			break;
		}
		bdd_or_accumulate(self->dd, &losing, U_star);
		bdd_free(self->dd, U_star);
		//

		// Is there a winning strategy staying inside reached?
		// Beware, in case of early exit, *win is not yet the fixpoint
		*win = bdd_synth_cpre_star(self, losing, universe, true);
		if ( bdd_included(self->dd, self->init, *win) ){
			break;
		}
		//}


		BddFsm_expand_cached_reachable_states(self->fsm, expand_steps, -1);
		prev_completed = BddFsm_get_cached_reachable_states(self->fsm, &layers, &new_diameter);

		// Update reached with new layers
		for (int i = diameter; i < new_diameter; i++){
			bdd_or_accumulate(self->dd, &reached, layers[i]);
		}

		// Update diameter
		diameter = new_diameter;
		
		universe = bdd_synth_over_approximate(self, reached, 1000);
	}while(!completed);

	bdd_free(self->dd, inputs);
	return realizable;
}

/**
 * Just backwards fp computation
 */
	/*
static boolean bdd_synth_backward_synth(BddSynth_ptr self, bdd_ptr * win){
		// The following version was for debug purposes
  boolean use_upre = true;
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
	*/

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
	bdd_ptr universe = bdd_synth_over_approximate(self, reachables, 1000);
	//
	*win = bdd_synth_cpre_star(self, self->error, universe, true);
	bdd_and_accumulate(self->dd, win, self->init);
	bdd_free(self->dd, universe);
	return bdd_isnot_false(self->dd, *win);
}


bdd_ptr bdd_synth_constrained_reachable_states(BddSynth_ptr self, bdd_ptr constraint){
	bdd_ptr prev_fp = bdd_false(self->dd);
	bdd_ptr fp = bdd_dup(self->init);
	while (prev_fp != fp){
		bdd_free(self->dd, prev_fp);
		prev_fp = fp;
		bdd_ptr newlayer = BddFsm_get_constrained_forward_image(self->fsm, fp, constraint);
		fp = bdd_or(self->dd, fp, newlayer);
		bdd_free(self->dd, newlayer);
	}
	return fp;
}



/**Function********************************************************************

   Synopsis    [Given relation(L,X_u,X_c), learn a function of given variable]

   Description []

   SideEffects []

   SeeAlso     []

******************************************************************************/
static bdd_ptr bdd_synth_extract_function_singlevar(BddSynth_ptr self, bdd_ptr relation, bdd_ptr variable){
	bdd_ptr ret_funct = NULL;
	// trueset := exists var. (relation & var) -- can be true
	bdd_ptr trueset = bdd_and_abstract(self->dd, relation, variable, variable);

	// Get exists var. (relation & ~var) -- can be false
	bdd_ptr not_v = bdd_not(self->dd, variable);
	bdd_ptr falseset = bdd_and_abstract(self->dd, relation, not_v, variable);

	bdd_ptr mustbetrue = bdd_not(self->dd, falseset);
	bdd_ptr mustbefalse= bdd_not(self->dd, trueset);
	bdd_ptr careset = bdd_or(self->dd, mustbetrue, mustbefalse);
	bdd_ptr appr_careset = bdd_synth_over_approximate(self, careset, 1000);

	bdd_ptr mbt_r = bdd_restrict(self->dd, mustbetrue, appr_careset);
	bdd_ptr mbf_r = bdd_restrict(self->dd, mustbefalse, appr_careset);

	// In ~mbt_r & ~v | mbt_r & v, variable must be set to true.
	bdd_ptr tmp = bdd_not(self->dd, mbt_r);
	bdd_and_accumulate(self->dd, &tmp, not_v);
	bdd_and_accumulate(self->dd, &mbt_r, variable);
	bdd_or_accumulate(self->dd, &mbt_r, tmp);
	bdd_ptr f1 = mbt_r; // just an alias
	bdd_free(self->dd, tmp);

	// In ~mbf_r & v | mbf_r & ~v, variable must be set to true.
	bdd_ptr ump = bdd_not(self->dd, mbf_r);
	bdd_and_accumulate(self->dd, &ump, variable);
	bdd_and_accumulate(self->dd, &mbf_r, not_v);
	bdd_or_accumulate(self->dd, &mbf_r, ump);
	bdd_ptr f2 = mbf_r; // just an alias
	bdd_free(self->dd, ump);

	// Choose the smallest and remove the other
	if ( Cudd_DagSize(f1) < Cudd_DagSize(f2) ){
		ret_funct = f1;
		bdd_free(self->dd, f2);
	} else {
		ret_funct = f2;
		bdd_free(self->dd, f1);
	}

	bdd_free(self->dd, mbt_r);
	bdd_free(self->dd, mbf_r);
	bdd_free(self->dd, appr_careset);
	bdd_free(self->dd, careset);
	bdd_free(self->dd, mustbetrue);
	bdd_free(self->dd, mustbefalse);
	bdd_free(self->dd, not_v);
	bdd_free(self->dd, trueset);
	bdd_free(self->dd, falseset);
	return ret_funct;
}

/**Function********************************************************************

   Synopsis    [Given relation(L,X_u,X_c), learn a function of inputs
	 						  that is included in relation.
								]

   Description [This is an implementation of Section 3.2.1 of Jiang et al.]

   SideEffects []

   SeeAlso     []

******************************************************************************/
static bdd_ptr bdd_synth_extract_function(BddSynth_ptr self, bdd_ptr relation, NodeList_ptr inputs){
	assert(NodeList_get_length(inputs)>0);
	// Create a table for projections
	int ninputs = NodeList_get_length(inputs);
	int i = 0;
	bdd_ptr * R = ALLOC(bdd_ptr, ninputs+1);
	bdd_ptr * F = ALLOC(bdd_ptr, ninputs+1);
	bdd_ptr * input_var = ALLOC(bdd_ptr, ninputs);
	for(i =0 ; i < ninputs; i++){
		R[i] = NULL;
		F[i] = NULL;
		input_var[i] = NULL;
	}
	// Transfer the list inputs to this array
  ListIter_ptr iter = NULL;
  for(iter = NodeList_get_first_iter(inputs);
			!ListIter_is_end(iter);
			iter = ListIter_get_next(iter))
	{
    node_ptr var = NodeList_get_elem_at(inputs,iter);
		input_var[i++] = BddEnc_expr_to_bdd(self->enc, var, Nil);
	}
	
	// Let R[i] := exists input_var[i..ninputs-1]. relation
	// We don't need R[0]
	R[ninputs] = relation;
	for(i = ninputs-1; i >= 1; i--){
		R[i] = bdd_forsome(self->dd, R[i+1], input_var[i]);
	}

	// compose table
	int nvars = Cudd_ReadSize(self->dd);
	bdd_ptr * comp_table = ALLOC(bdd_ptr, nvars);
	for(i = 0; i < nvars; i++){
		comp_table[i] = Cudd_bddIthVar(self->dd, i);
	}

	// After iteration i, F[i-1] will be a function of input_var[0..i-1]
	for(i = 1; i <= ninputs; i++){
		bdd_ptr R_composed = bdd_vector_compose(self->dd, R[i], comp_table);
		F[i-1] = bdd_synth_extract_function_singlevar(self, R_composed, input_var[i-1]);
		unsigned int var_index = Cudd_NodeReadIndex(input_var[i-1]);
		comp_table[var_index] = F[i-1];
	}
	bdd_ptr f = bdd_dup(F[ninputs]);
	// Clean up
	free(comp_table);
	for(i = 0; i <= ninputs; i++){
		if (!R[i]){
			bdd_free(self->dd, R[i]);
		}
		if (!F[i]){
			bdd_free(self->dd, F[i]);
		}
		if (i < ninputs){
			bdd_free(self->dd, input_var[i]);
		}
	}
	free(R);
	free(F);
	free(input_var);
	if (!bdd_implies(self->dd, f, relation) ){
		assert("function f not a subset of relation" == 0);
	}
	return f;
}

static boolean bdd_synth_learnAlgo1(BddSynth_ptr self, bdd_ptr * win){
	bdd_ptr W = bdd_not(self->dd, self->error);
	bdd_ptr P;
	bdd_ptr R;
	boolean realizable = false;
	while(1){
		bdd_ptr f = bdd_synth_extract_function(self, W, self->cinputs);
		R = bdd_synth_constrained_reachable_states(self, f);
		if ( bdd_implies(self->dd, R, W) ){
			bdd_free(self->dd, f);
			bdd_free(self->dd, R);
			realizable = true;
			break;
		}
		bdd_ptr R_notW = bdd_not(self->dd, W);
		bdd_and_accumulate(self->dd, &R_notW, R);
		P = BddFsm_get_backward_image(self->fsm, R_notW);
		bdd_and_accumulate(self->dd, &P, f);
		bdd_ptr notP = bdd_not(self->dd, P);
		bdd_and_accumulate(self->dd, &W, notP);

		bdd_free(self->dd, f);
		bdd_free(self->dd, R);
		bdd_free(self->dd, R_notW);
		bdd_free(self->dd, P);
		bdd_free(self->dd, notP);
		
		// Check if init <= W. If not, return unreal
		bdd_ptr tmp = bdd_and(self->dd, W, self->init);
		if (bdd_is_false(self->dd, tmp)){
			realizable = false;
			bdd_free(self->dd, tmp);
			break;
		}		
		bdd_free(self->dd, tmp);
	}
	*win = W;
	return realizable;
}


EXTERN boolean BddSynth_solve(const BddSynth_ptr self, BddSynth_dir mode, bdd_ptr * win){
  boolean ret;
  switch(mode){
		case BDD_SYNTH_DIR_BWD:
			printf("Backward algorithm\n");
			*win = bdd_synth_cpre_star(self, self->error, bdd_true(self->dd), true);
			ret = bdd_included(self->dd, self->init, *win);
			break;
		case BDD_SYNTH_DIR_BWD_W_REACH:
			printf("Backward algorithm with forward reach states reduction\n");
			ret = bdd_synth_backward_synth_reach(self, win);
			break;
		case BDD_SYNTH_DIR_FWD:
			printf("Forward algorithm\n");
			ret = bdd_synth_forward_backward_synth(self, win);
			break;
		case BDD_SYNTH_DIR_LEARNING1:
			printf("Iterative learning algorithm 1\n");
			ret = bdd_synth_learnAlgo1(self, win);
		default:
			ret = false;
	}
	return ret;
}


/* TODO Just compute the reachable states using the following function:
 * 
BddStates
BddFsm_get_constrained_forward_image(const BddFsm_ptr self,
                                     BddStates states,
                                     BddStatesInputsNexts constraints)
 *
 *
 *
 */
/* The following is an attempt at obtaining a new transition relation by
 * reclustering the transition functions for latches.
 * Is this more efficient than using the constrained_forward_image function ? 
 * */
/*
BddTrans_ptr make_constrained_trans(const BddSynth_ptr self, bdd_ptr constraint){
	// Make a cluster out of constrained transition relations
	BddTrans_ptr newtrans = BDD_TRANS(NULL);
	ClusterOptions_ptr cluster_options;
	ClusterList_ptr clusters = ClusterList_create(self->dd);
	cluster_options = ClusterOptions_create(OptsHandler_get_instance());

	bdd_ptr v_elm;
	bdd_ptr v_elm_primed;
	bdd_ptr constrained_t;
	bdd_ptr T_v;
	unsigned int vindex = 0;
	ListIter_ptr v = NodeList_get_first_iter(self->latches);
	for(; !ListIter_is_end(v); v = ListIter_get_next(v)){
		v_elm = (bdd_ptr)NodeList_get_elem_at(self->latches, v);
		vindex = Cudd_NodeReadIndex(v_elm);
		assert(vindex >= 0 && vindex < Cudd_ReadSize(self->dd));
		assert(self->trans[vindex] != NULL);
		v_elm_primed = BddEnc_state_var_to_next_state_var(self->enc, v_elm);
		constrained_t = bdd_and(self->dd, self->trans[vindex], constraint);
		T_v = bdd_iff(self->dd, v_elm_primed, constrained_t);
		// T_v := v' <-> trans[v] /\ constraint
		bdd_free(self->dd, v_elm_primed);
		bdd_free(self->dd, constrained_t);

		Cluster_ptr cluster = Cluster_create(self->dd);
		Cluster_set_trans(cluster, self->dd, T_v);
		ClusterList_append_cluster(clusters, cluster);
	}
	// We also add the inputs to the cluster since they are seen as variables

	bdd_ptr input_cube = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);
	bdd_ptr platch_cube = BddEnc_next_state_var_to_state_var(self->enc, self->latch_cube);
	newtrans = BddTrans_create(self->dd,
													clusters,
													self->latch_cube,
													input_cube,
													platch_cube,
													TRANS_TYPE_IWLS95,
													cluster_options);
	ClusterList_destroy(clusters);
	ClusterOptions_destroy(cluster_options); // this is no longer needed
	return newtrans;
}
*/
