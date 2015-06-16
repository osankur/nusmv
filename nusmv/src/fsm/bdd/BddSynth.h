/**CHeaderFile*****************************************************************

  FileName    [BddSynth.h]

  PackageName [fsm.bdd]

  Synopsis    [Declares the interface of the class BddSynth]

  Description [This module implements backwards and forward algorithms
              for synthesis. ]
  
  Author      [Ocan Sankur]
*/
#ifndef __FSM_BDD_BDD_SYNTH_H__
#define __FSM_BDD_BDD_SYNTH_H__

#include "bdd.h"
#include "BddFsm.h"

#include "utils/utils.h"  /* for EXTERN and ARGS */
#include "dd/dd.h"
#include "trans/bdd/BddTrans.h"
#include "enc/bdd/BddEnc.h" /* Encoding */
#include "fsm/sexp/sexp.h" /* VarSet_ptr */


typedef struct BddSynth_TAG*  BddSynth_ptr;

#define BDD_SYNTH(x) \
         ((BddSynth_ptr) x)

#define BDD_SYNTH_CHECK_INSTANCE(x) \
         (nusmv_assert( BDD_SYNTH(x) != BDD_SYNTH(NULL) ))

enum Bdd_Synth_dir_TAG {BDD_SYNTH_DIR_BWD, BDD_SYNTH_DIR_FWD};
typedef enum Bdd_Synth_dir_TAG BddSynth_dir;

/* ---------------------------------------------------------------------- */
/* public interface                                                       */
/* ---------------------------------------------------------------------- */
EXTERN BddSynth_ptr BddSynth_create ARGS((BddFsm_ptr fsm));
EXTERN void BddSynth_destroy ARGS((BddSynth_ptr self));
EXTERN boolean BddSynth_solve ARGS((const BddSynth_ptr self, BddSynth_dir mode, bdd_ptr * win));


#endif
