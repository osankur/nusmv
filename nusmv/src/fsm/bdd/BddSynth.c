/*
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

#define BDD_SYNTH_BDD_THRESHOLD 1000

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
	if ( Cudd_DagSize(f) <= threshold ) {
		return bdd_dup(f);
	} else 
		return bdd_over_approx(self->dd, f, numVars, threshold, 1, 0.5);
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


static void dump_tmp_and_wait(BddSynth_ptr self, bdd_ptr nextFront, char * name){
    char * labels = name;
    FILE * outfile = fopen("/tmp/a.dot", "w");
    if (!outfile){
      return;
    }
    AddArray_ptr ar = AddArray_create(1);
    AddArray_set_n(ar,0,bdd_to_add(self->dd, nextFront));
    BddEnc_dump_addarray_dot(self->enc, ar, (const char **)&labels, outfile);
    fclose(outfile);
    // while(getchar() != 'c');
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

static boolean bdd_synth_contains_init(BddSynth_ptr self, bdd_ptr s){
	bdd_ptr tmp = bdd_dup(s);
	bdd_and_accumulate(self->dd, &tmp, self->init);
	boolean ret = !bdd_is_false(self->dd, tmp);
	bdd_free(self->dd, tmp);
	return ret;
}

/** Compute states reachable from the initial state along transitions
 * constrained by constraint, and (if incr_approx) by applying
 * over-approximation every appr_period steps. */
bdd_ptr bdd_synth_constrained_reachable_states(BddSynth_ptr self, bdd_ptr constraint, bool incr_approx){
	int appr_period = 2;
	bdd_ptr prev_fp = bdd_false(self->dd);
	bdd_ptr fp = bdd_dup(self->init);
	printf("Computing reachables states");
	int count = 0;
	while (prev_fp != fp){
		count++;
		if (incr_approx & (count % appr_period == 0)){
			bdd_ptr tmp = bdd_synth_over_approximate(self, fp, 1000);
			bdd_free(self->dd, fp);
			fp = tmp;
		}
		printf("."); fflush(stdout);
		bdd_free(self->dd, prev_fp);
		prev_fp = bdd_dup(fp);
		bdd_ptr newlayer = BddFsm_get_constrained_forward_image(self->fsm, fp, constraint);
		bdd_or_accumulate(self->dd, &fp, newlayer);
		bdd_free(self->dd, newlayer);
	}

	// Project away inputs (this is because inputs are encoded as state variables)
	bdd_ptr inputs_cube = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);
	bdd_ptr tmp = bdd_forsome(self->dd, fp, inputs_cube);
	bdd_free(self->dd, fp);
	fp = tmp;

	if (incr_approx && Cudd_DagSize(fp) > 1000){
			bdd_ptr tmp = bdd_synth_over_approximate(self, fp, 1000);
			bdd_free(self->dd, fp);
			fp = tmp;
	}
	printf("\n");
	return fp;
}





static bdd_ptr bdd_synth_cpre_trans(BddSynth_ptr self, bdd_ptr states, bdd_ptr * trans, boolean use_restrict)
{
	int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * local_trans = trans;
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
	// vector_compose seems quite faster in general compared to partitioned trans
	// relation
	// bdd_ptr pre1 = BddFsm_get_backward_image(self->fsm, pstates);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, local_trans);
  bdd_ptr pre2 = bdd_forsome(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forall(self->dd, pre2, self->uinput_cube);
  bdd_free(self->dd, pstates);
  bdd_free(self->dd, pre2);
  bdd_free(self->dd, pre1);
  return pre3;
}

/** TODO This was just an attempt; currently not working*/
/** Upre computation with custom transition relation vector */
static bdd_ptr bdd_synth_cpre_clustered(BddSynth_ptr self, bdd_ptr states){
	// Put all BDD variable indices that correspond to latches into an array
	int nlatches = NodeList_get_length(self->latches);
	unsigned int * latch_indices = (unsigned int*) malloc(nlatches * sizeof(unsigned int));
	for(int i = 0; i < nlatches; i++){
		latch_indices[i] = 0;
	}
  ListIter_ptr iter = NodeList_get_first_iter(self->latches);
	int i = 0;
  NODE_LIST_FOREACH(self->latches,iter){
    node_ptr var = NodeList_get_elem_at(self->latches,iter);
    bdd_ptr varbdd = BddEnc_expr_to_bdd(self->enc, var, Nil);
		unsigned int var_index = Cudd_NodeReadIndex(varbdd);
		latch_indices[i++] = var_index;
	}
	// Sort that array for the size of the next-state function
	for(i = 0; i < nlatches; i++){
		for(int j = i+1; j < nlatches; j++){
			if( Cudd_DagSize(self->trans[ latch_indices[i] ]) > 
					Cudd_DagSize(self->trans[ latch_indices[j] ])){
				int tmp = latch_indices[i];
				latch_indices[i] = latch_indices[j];
				latch_indices[j] = tmp;
			}
		}
	}

	// Create an array of local trans relations l' <-> T_l
	bdd_ptr * pvars = ALLOC(bdd_ptr, nlatches);
	bdd_ptr * rels = ALLOC(bdd_ptr, nlatches);
	for(i = 0; i < nlatches; i++){
		pvars[i] = BddEnc_state_var_to_next_state_var(self->enc, Cudd_bddIthVar(self->dd, latch_indices[i]));
		rels[i] = bdd_iff(self->dd, self->trans[i], pvars[i]);
	}

  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
	bdd_ptr pre1 = NULL;
	// P = .... ∃ l_{n-1}' (∃ l_n'. S(L') /\ T_n) /\ T_{n-1}
	for(i = 0; i < nlatches; i++){
		// intersect with rels[i] and abstract pvars[i] away
		pre1 = bdd_and_abstract(self->dd, pstates, rels[i], pvars[i]);
		bdd_free(self->dd, pstates);
		pstates = pre1;
	}
	/*
	 * The version with full trans rel for debugging
	for(i = 0; i < nlatches; i++){
		// intersect with rels[i] and abstract pvars[i] away
		bdd_and_accumulate(self->dd, &pstates, rels[i]);
	}
	for(i = 0; i < nlatches; i++){
		pre1 = bdd_forsome(self->dd, pstates, pvars[i]);
		bdd_free(self->dd, pstates);
		pstates = pre1;
	}
	*/
  bdd_ptr pre2 = bdd_forsome(self->dd, pstates, self->cinput_cube);
  bdd_ptr pre3 = bdd_forall(self->dd, pre2, self->uinput_cube);
	// Clean up
  bdd_free(self->dd,pre2);
  bdd_free(self->dd,pstates);

	free(latch_indices);
	free(rels);
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
	bdd_ptr * restricted_trans = NULL;
	// Restrict the transition relation to (universe /\ ~start)(L)
	restricted_trans = ALLOC(bdd_ptr, n);
	bdd_ptr universe_not_start = bdd_not(self->dd, start);
	bdd_and_accumulate(self->dd, &universe_not_start, universe);
	bdd_ptr appr_universe_not_start = bdd_synth_over_approximate(self, universe_not_start, 1000);
	bdd_free(self->dd, universe_not_start);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_safe_restrict(self->dd, self->trans[i], appr_universe_not_start);
	}
	bdd_free(self->dd, appr_universe_not_start);
  print_trans_size_cstm(self, restricted_trans);
	// restricted_trans = self->trans;
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
 *
 *
 */ 
static bdd_ptr bdd_synth_cpre_star(BddSynth_ptr self, bdd_ptr losing, bdd_ptr universe, boolean early_exit){
	int n = Cudd_ReadSize(self->dd);
	int cnt = 1;
	bdd_ptr notlosing = bdd_not(self->dd, losing);

	bdd_ptr * restricted_trans = self->trans;
	// TODO The below restriction is incorrect. Find out why
	// Restrict the transition relation to (an overapprox of) notlosing & universe(L)
	/*
	bdd_ptr * restricted_trans = ALLOC(bdd_ptr, n);
	bdd_and_accumulate(self->dd, &notlosing, universe);
	bdd_ptr appr_notlosing_and_universe = bdd_synth_over_approximate(self, notlosing, 1000);
	for (int i = 0; i < n ; i++){
		restricted_trans[i] = bdd_safe_restrict(self->dd, self->trans[i], appr_notlosing_and_universe);
  }
	bdd_free(self->dd, appr_notlosing_and_universe);
  print_trans_size_cstm(self, restricted_trans);
	*/
	bdd_ptr iterate = bdd_and(self->dd, universe, notlosing);
	bdd_ptr prev = NULL;
	printf("\tStarting CPRE fixpoint\n");
	printf("Iterate contains init: %d\n", bdd_included(self->dd, self->init, iterate));
	while( iterate != prev ){
		printf("\tCpre iteration %d (iterate size: %d)\n", cnt++, Cudd_DagSize(iterate));
		if (prev) bdd_free(self->dd, prev);
		prev = iterate;
		iterate = bdd_synth_cpre_trans(self, prev, restricted_trans, true);
		/*
		// TESTING
		bdd_ptr next_ = bdd_synth_cpre_clustered(self, prev);
		printf("classical next: %d, modern next: %d\n", Cudd_DagSize(iterate), Cudd_DagSize(next_));
		assert(iterate== next_);
		bdd_free(self->dd, next_);
		//
		*/
		if ( !bdd_synth_contains_init(self, iterate) ){
			break;
		}
		bdd_and_accumulate(self->dd, &iterate, prev);
    bdd_and_accumulate(self->dd, &iterate, universe);
		assert(bdd_included(self->dd, iterate, prev));
	}
	bdd_free(self->dd, prev);
	bdd_free(self->dd, notlosing);
	/*
	for (int i = 0; i < n ; i++){
		bdd_free(self->dd, restricted_trans[i]);
	}
	free(restricted_trans);
	*/
	return iterate;
}

/**
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
	bdd_ptr reached = bdd_dup(self->init);
	//bdd_ptr reached = bdd_false(self->dd);
	bdd_ptr universe = bdd_dup(reached); // an over-approx. of reached
	int cnt = 1;
	// how many reachability layers we explore at each step
	int expand_steps = 4; 
	boolean completed = false;
	boolean prev_completed = false;
	int diameter = 0;
	int new_diameter;
	BddStates* layers;
	bdd_ptr inputs = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);

	printf("\tExpand steps = %d\n", expand_steps);
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


		BddFsm_expand_cached_reachable_states(self->fsm, expand_steps, -1);
		prev_completed = BddFsm_get_cached_reachable_states(self->fsm, &layers, &new_diameter);

		// Update reached with new layers
		for (int i = diameter; i < new_diameter; i++){
			bdd_or_accumulate(self->dd, &reached, layers[i]);
		}

		// Update diameter
		diameter = new_diameter;
		
		bdd_free(self->dd, universe);
		universe = bdd_synth_over_approximate(self, reached, 1000);
	}while(!completed);

	bdd_free(self->dd, inputs);
	return realizable;
}

/** Returns Approximation of the set S \/ \/_{1<= i <= k} post^i(S)
 *
 *  During the computation, whenever the BDD size exceeds
 *  2*BDD_SYNTH_BDD_THRESHOLD, we apply approximation to reduce it back.
 *
 * */
bdd_ptr bdd_synth_add_postk(BddSynth_ptr self, bdd_ptr S, bdd_ptr constraint, int k, int * expanded_by, boolean incr_approx){
	bdd_ptr prev_fp = NULL;
	bdd_ptr fp = bdd_dup(S);
	printf("Computing reachables states: ");
	*expanded_by = 0;
	do{
		if (prev_fp) bdd_free(self->dd, prev_fp);
		prev_fp = fp;
		bdd_ptr newlayer = BddFsm_get_constrained_forward_image(self->fsm, fp, constraint);
		fp = bdd_or(self->dd, fp, newlayer);
		bdd_free(self->dd, newlayer);
		if ( prev_fp != fp ){
			(*expanded_by)++;
		}
		if (incr_approx && (Cudd_DagSize(fp) > 2 * BDD_SYNTH_BDD_THRESHOLD) ){
			printf("Bdd size has reached: %d. Approximating...\n", Cudd_DagSize(fp));
			bdd_ptr tmp = bdd_synth_over_approximate(self, fp, 1000);
			bdd_free(self->dd, fp);
			fp = tmp;
		}
		printf("."); fflush(stdout);
	} while (prev_fp != fp && (k < 0 || *expanded_by < k));

	printf("\n");
	return fp;
}

/*
 * Same algorithm as the above forward-backward one but using 
 * the postk function above to compute approximations of forward reachable
 * states
 *
 */
static boolean bdd_synth_forward_backward_synth_tmp(BddSynth_ptr self, bdd_ptr * win){
	boolean approx_reach = false;
	boolean realizable = true;
	bdd_ptr losing = bdd_dup(self->error); // under-approximation of losing region; contains error
	bdd_ptr reached = bdd_dup(self->init); // currently reachable states
	int cnt = 1;
	// how many reachability layers we explore at each step
	int expand_steps = 4; 
	boolean completed = false;
	boolean prev_completed = false;
	int diameter = 0;
	int new_diameter;
	BddStates* layers;
	bdd_ptr inputs = bdd_and(self->dd, self->cinput_cube, self->uinput_cube);

	printf("\tExpand steps = %d\n", expand_steps);
	do {
		printf("Forward image iteration %d (Diameter: %d, (Appr : %d) Reached size: %d) \n", cnt++, diameter, approx_reach, Cudd_DagSize(reached));
		completed = prev_completed;

		// Is there a counter-strategy staying inside reached?
		bdd_ptr U_star = bdd_synth_upre_star(self, losing, reached, true);
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
		*win = bdd_synth_cpre_star(self, losing, reached, true);
		if ( bdd_included(self->dd, self->init, *win) ){
			break;
		}

		bdd_ptr newlayer = bdd_synth_add_postk(self, reached, bdd_true(self->dd), expand_steps, &new_diameter, approx_reach);
		bdd_free(self->dd, reached);
		reached = newlayer;

		// Update diameter
		diameter += new_diameter;
		
	}while(!completed);

	bdd_free(self->dd, inputs);
	return realizable;
}


/**Function********************************************************************

   Synopsis    [Compute an over-approximation of the reachable states, and 
	 							constrain the CPRE* to this universe.]

   Description []

   SideEffects []

   SeeAlso     []

******************************************************************************/
static boolean bdd_synth_backward_synth_reach(BddSynth_ptr self, bdd_ptr * win){
  BddStates* layers;
	int diameter;
	boolean incr_appr = true;

  // Debug log
  print_trans_size(self);

	bdd_ptr reachables = bdd_false(self->dd);
	if (!incr_appr){
		BddFsm_expand_cached_reachable_states(self->fsm, -1, -1);
		boolean completed = BddFsm_get_cached_reachable_states(self->fsm, &layers, &diameter);
		for(int i = 0; i < diameter; i++){
			bdd_or_accumulate(self->dd, &reachables, layers[i]);
		}
	} else {	
		int diameter;
		reachables = bdd_synth_add_postk(self, self->init, bdd_true(self->dd), -1, &diameter, true);
		// reachables = bdd_synth_constrained_reachable_states(self, bdd_true(self->dd), true);
	}

	printf("Reachable states computed. DagSize: %d Diameter: %d\n", Cudd_DagSize(reachables), diameter);
	// bdd_ptr universe = bdd_synth_over_approximate(self, reachables, 1000);
	bdd_ptr universe = bdd_dup(reachables);
	bdd_free(self->dd, reachables);
	printf("\tAppr universe has dag size: %d\n", Cudd_DagSize(universe));
	*win = bdd_synth_cpre_star(self, self->error, universe, true);
	bdd_free(self->dd, universe);
	return bdd_included(self->dd, self->init, *win);
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

	 TODO 			 [ How to speed up this. Implement the other variant from Jiang et al.]

******************************************************************************/
static bdd_ptr bdd_synth_extract_function(BddSynth_ptr self, bdd_ptr relation, NodeList_ptr inputs){
	assert(NodeList_get_length(inputs)>0);
	// Create a table for projections
	int ninputs = NodeList_get_length(inputs);
	int i;
	bdd_ptr * R = ALLOC(bdd_ptr, ninputs+1);
	bdd_ptr * F = ALLOC(bdd_ptr, ninputs);
	bdd_ptr * input_var = ALLOC(bdd_ptr, ninputs);
	for(i =0 ; i <= ninputs; i++){
		R[i] = NULL;
		if (i < ninputs){
			F[i] = NULL;
			input_var[i] = NULL;
		}
	}
	// Transfer the list inputs to this array
  ListIter_ptr iter = NULL;
	i = 0;
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
	bdd_ptr f = bdd_dup(F[ninputs-1]);
	// Clean up
	free(comp_table);
	for(i = 0; i <= ninputs; i++){
		if (R[i]){
			bdd_free(self->dd, R[i]);
		}
		if (i < ninputs){
			bdd_free(self->dd, input_var[i]);
			if (F[i]){
				bdd_free(self->dd, F[i]);
			}
		}
	}
	free(R);
	free(F);
	free(input_var);
	bdd_ptr tmp = bdd_not(self->dd, relation);
	bdd_and_accumulate(self->dd, &tmp, f);
	if ( bdd_isnot_false(self->dd, tmp) ){
		fprintf(nusmv_stderr, "Function not included in relation!\n");
	}
	return f;
}

/*
 * FIXME Cudd reference count error!
 */
static boolean bdd_synth_learnAlgo1(BddSynth_ptr self, bdd_ptr * win){
	int iteration_count = 0;
	bdd_ptr W = bdd_not(self->dd, self->error);
	bdd_ptr P;
	bdd_ptr R;
	boolean realizable = false;
	while(1){
		iteration_count++;
		printf("Extracting function...\n"); fflush(stdout);
		bdd_ptr f = bdd_synth_extract_function(self, W, self->cinputs);

		printf("Computing reachable states...\n"); fflush(stdout);
		R = bdd_synth_constrained_reachable_states(self, f, false);
		// TODO Attention R(L) 

		if ( bdd_included(self->dd, R, W) ){
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
		if (!bdd_included(self->dd, self->init, W)){
			realizable = false;
			break;
		}
	}
	*win = W;
	printf("Returned after %d iterations\n", iteration_count);
	printf("init \\in W: %d\n", bdd_included(self->dd, self->init, W));
	return realizable;
}
static void check_invar(BddSynth_ptr self, int steps){
	int count = 0;
	bdd_ptr reach = NULL, tmp = NULL;
	bdd_ptr prev = BddFsm_get_init(self->fsm);
	reach = bdd_dup(prev);
	printf("Computing reachable states up to steps %d\n", steps);
	for(count = 0; count < steps | steps < 0; count++){
		printf("Step: %d, bdd size: %d\n", count, Cudd_DagSize(prev));
		tmp = BddFsm_get_forward_image(self->fsm, prev);
		bdd_or_accumulate(self->dd, &reach, prev);
		if (prev == reach){
			bdd_free(self->dd,prev);
			break;
		}
		bdd_free(self->dd, prev);
		prev = reach;
	}
	printf("We did %d iterations\n", count);
}



/** Learning without extracting functions 
 *
 * Here the idea was to use W as a quasi-strategy,
 * and iteratively remove the predecessors of R\W.
 * This is somehow close to UPRE (several iterations are needed for one UPRE)
 * but it is not clear how the alternation of quantifiers can be implemented.
 * */
/*
static boolean bdd_synth_learnAlgo2(BddSynth_ptr self, bdd_ptr * win){
	int iteration_count = 0;
	bdd_ptr allinputs_cube = bdd_and(self->dd, self->uinputs, self->cinputs);
	bdd_ptr W = bdd_not(self->dd, self->error);
	bdd_ptr P;
	bdd_ptr R;
	boolean realizable = false;
	while(1){
		iteration_count++;
		bdd_ptr pW = bdd_forsome(self->dd, W, allinputs_cube);
		bdd_ptr B = bdd_not(self->dd, pW);
		bdd_and_accumulate(self->dd, &B, R);

		R = bdd_synth_constrained_reachable_states(self, f);
		if ( bdd_included(self->dd, R, W) ){
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
		if (!bdd_included(self->dd, self->init, W)){
			realizable = false;
			break;
		}
	}
	*win = W;
	bdd_free(self->dd, allinputs_cube);
	printf("Returned after %d iterations\n", iteration_count);
	printf("init \\in W: %d\n", bdd_included(self->dd, self->init, W));
	return realizable;
}
*/

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
			ret = bdd_synth_forward_backward_synth_tmp(self, win);
			// ret = bdd_synth_forward_backward_synth_tmp(self, win);
			break;
		case BDD_SYNTH_DIR_LEARNING1:
			printf("Hijacked for Model checking!\n");
			check_invar(self, -1);
			// printf("Iterative learning algorithm 1\n");
			// ret = bdd_synth_learnAlgo1(self, win);
			// printf("Decision realizable: %d\n", bdd_included(self->dd, self->init, *win));
			// printf("Returned %d\n", ret);
			break;
		default:
			fprintf(nusmv_stderr, "Unknown solve mode\n");
			exit(-1);
	}
	return ret;
}



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

