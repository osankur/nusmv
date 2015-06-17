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
static bdd_ptr bdd_synth_cpre ARGS((BddSynth_ptr self, bdd_ptr states));

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
  // TODO We could free trans_rels at this point
  // TODO free trans_funcs at the end

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
static bdd_ptr bdd_synth_cpre(BddSynth_ptr self, bdd_ptr states){
  bdd_ptr * local_trans = self->trans;
#ifdef RESTRICT_IN_CPRE
  bdd_ptr notstates = bdd_not(self->dd, states);
  int nvar = Cudd_ReadSize(self->dd);
  bdd_ptr * Y = ALLOC(bdd_ptr, nvar);
  int i;
  for (i = 0; i < nvar; i++){
    Y[i] = bdd_restrict(self->dd, self->trans[i], notstates);
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
static bdd_ptr bdd_synth_upre(BddSynth_ptr self, bdd_ptr states){
  bdd_ptr pstates = BddEnc_state_var_to_next_state_var(self->enc, states);
  bdd_ptr pre1 = bdd_vector_compose(self->dd, pstates, self->trans);
  bdd_ptr pre2 = bdd_forall(self->dd, pre1, self->cinput_cube);
  bdd_ptr pre3 = bdd_forsome(self->dd, pre2, self->uinput_cube);
  bdd_free(self->dd,pre2);
  bdd_free(self->dd,pre1);
  bdd_free(self->dd,pstates);
  return pre3;
}
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

static boolean bdd_synth_backward_synth(BddSynth_ptr self, bdd_ptr * win){
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

EXTERN boolean BddSynth_solve(const BddSynth_ptr self, BddSynth_dir mode, bdd_ptr * win){
  boolean ret;
  switch(mode){
		case BDD_SYNTH_DIR_BWD:
			printf("Backward algorithm\n");
			ret = bdd_synth_backward_synth(self, win);
			break;
		case BDD_SYNTH_DIR_FWD:
			printf("Forward algorithm\n");
		default:
			ret = false;
	}
	return ret;
}
