#!/bin/bash

# This is a benchmark framework that may be useful for evaluating
# synthesis tools developed for SyntComp.
#
# Version: 1.0.1
# Created by Robert Koenighofer, robert.koenighofer@iaik.tugraz.at
# Comments/edits by Swen Jacobs, swen.jacobs@iaik.tugraz.at

# This directory:
DIR=`dirname $0`/

# Time limit in seconds:
TIME_LIMIT=320
# Memory limit in kB:
MEMORY_LIMIT=2000000

# Maybe change the following line to point to GNU time:
GNU_TIME="time"
MODEL_CHECKER="$DIR/../blimc/blimc"
SYNT_CHECKER="$DIR/../aiger/syntactic_checker.py"

# The directory where the benchmarks are located:
BM_DIR="/home/sankur/work/ulb/syntcomp/bench-syntcomp14/smv/"

REAL=10
UNREAL=20

# The benchmarks to be used.
# The files have to be located in ${BM_DIR}.
FILES=(
#genbuf8f8n.smv $REAL
#genbuf9c3y.smv $REAL
#genbuf4b3unrealy.smv $UNREAL
#genbuf14b3unrealn.smv $UNREAL
#genbuf2f4n.smv $REAL
#genbuf1c3y.smv $REAL
#genbuf11b3unrealn.smv $UNREAL
#genbuf11f11y.smv $REAL
#genbuf15c3n.smv $REAL
#genbuf13b3unrealy.smv $UNREAL
#genbuf10c3y.smv $REAL
#genbuf10c2unrealn.smv $UNREAL
#genbuf6f6n.smv $REAL
#genbuf15c3y.smv $REAL
#genbuf5c3y.smv $REAL
#genbuf16c3n.smv $REAL
#genbuf15f14unrealy.smv $UNREAL
#genbuf16c2unrealn.smv $UNREAL
#genbuf5c3n.smv $REAL
#genbuf11b4n.smv $REAL
#genbuf1b4y.smv $REAL
#genbuf6c3y.smv $REAL
#genbuf8f7unrealn.smv $UNREAL
#genbuf5b3unrealy.smv $UNREAL
#genbuf15f14unrealn.smv $UNREAL
#genbuf9b4y.smv $REAL
#genbuf6f5unrealy.smv $UNREAL
#genbuf2f3unrealn.smv $UNREAL
#genbuf11b3unrealy.smv $UNREAL
#genbuf4c2unrealn.smv $UNREAL
#genbuf1f3unrealn.smv $UNREAL
#genbuf9f8unrealy.smv $UNREAL
#genbuf8b4y.smv $REAL
#genbuf10b4y.smv $REAL
#genbuf16b3unrealy.smv $UNREAL
#genbuf12c3n.smv $REAL
#genbuf14c3n.smv $REAL
#genbuf15c2unrealy.smv $UNREAL
#genbuf12f11unrealy.smv $UNREAL
#genbuf7f7y.smv $REAL
#genbuf1f3unrealy.smv $UNREAL
#genbuf5f5n.smv $REAL
#genbuf9b4n.smv $REAL
#genbuf8f7unrealy.smv $UNREAL
#genbuf15f15n.smv $REAL
#genbuf7f6unrealn.smv $UNREAL
#genbuf13c2unrealn.smv $REAL
#genbuf2b4n.smv $REAL
#genbuf4b4n.smv $REAL
#genbuf16b4n.smv $REAL
#genbuf1f4n.smv $REAL
#genbuf3f4n.smv $REAL
#genbuf13b4y.smv $REAL
#genbuf16b4y.smv $REAL
#genbuf6b3unrealy.smv $UNREAL
genbuf3b4y.smv $REAL
genbuf14b4n.smv $REAL
genbuf5f5y.smv $REAL
genbuf1c3n.smv $REAL
genbuf16f15unrealy.smv $UNREAL
genbuf7f6unrealy.smv $UNREAL
genbuf13c3y.smv $REAL
genbuf13c2unrealy.smv $UNREAL
genbuf13b4n.smv $REAL
genbuf14f13unrealn.smv $UNREAL
genbuf2c3n.smv $REAL
genbuf13b3unrealn.smv $UNREAL
genbuf14c2unrealn.smv $UNREAL
genbuf15f15y.smv $REAL
genbuf12b3unrealy.smv $UNREAL
genbuf10f10n.smv $REAL
genbuf4c3y.smv $REAL
genbuf3f3unrealn.smv $UNREAL
genbuf14f13unrealy.smv $UNREAL
genbuf12c2unrealn.smv $UNREAL
genbuf3b4n.smv $REAL
genbuf11c3y.smv $REAL
genbuf8c3y.smv $REAL
genbuf9f8unrealn.smv $UNREAL
genbuf3c2unrealn.smv $UNREAL
genbuf4b4y.smv $REAL
genbuf13f12unrealn.smv $UNREAL
genbuf8b4n.smv $REAL
genbuf1b3unrealn.smv $UNREAL
genbuf1f4y.smv $REAL
genbuf3c3n.smv $REAL
genbuf2b4y.smv $REAL
genbuf11f10unrealy.smv $UNREAL
genbuf9c3n.smv $REAL
genbuf8c3n.smv $REAL
genbuf2c2unrealy.smv $UNREAL
genbuf14f14n.smv $REAL
genbuf11c3n.smv $REAL
genbuf9c2unrealy.smv $UNREAL
genbuf3f4y.smv $REAL
genbuf12b3unrealn.smv $UNREAL
genbuf8c2unrealy.smv $UNREAL
genbuf15b4n.smv $REAL
genbuf8b3unrealn.smv $UNREAL
genbuf16f16y.smv $REAL
genbuf11f10unrealn.smv $UNREAL
genbuf5c2unrealy.smv $UNREAL
genbuf4f3unrealn.smv $UNREAL
genbuf7b4y.smv $REAL
genbuf12f12n.smv $REAL
genbuf7b3unrealn.smv $UNREAL
genbuf10c3n.smv $REAL
genbuf4f4n.smv $REAL
genbuf8c2unrealn.smv $UNREAL
genbuf12c2unrealy.smv $UNREAL
genbuf5b4y.smv $REAL
genbuf10b3unrealn.smv $UNREAL
genbuf7c2unrealy.smv $UNREAL
genbuf10b4n.smv $REAL
genbuf2c3y.smv $REAL
genbuf8f8y.smv $REAL
genbuf2b3unrealy.smv $UNREAL
genbuf4b3unrealn.smv $UNREAL
genbuf4c3n.smv $REAL
genbuf13f13y.smv $REAL
genbuf4f3unrealy.smv $UNREAL
genbuf3b3unrealn.smv $UNREAL
genbuf2b3unrealn.smv $UNREAL
genbuf5f4unrealy.smv $UNREAL
genbuf12b4y.smv $REAL
genbuf2f3unrealy.smv $UNREAL
genbuf9b3unrealy.smv $UNREAL
genbuf6b4y.smv $REAL
genbuf11b4y.smv $REAL
genbuf15b4y.smv $REAL
genbuf14f14y.smv $REAL
genbuf15c2unrealn.smv  $UNREAL
genbuf3c2unrealy.smv $UNREAL
genbuf5b4n.smv $REAL
genbuf4f4y.smv $REAL
genbuf9c2unrealn.smv $UNREAL
genbuf2f4y.smv $REAL
genbuf7c3n.smv $REAL
genbuf7b4n.smv $REAL
genbuf5f4unrealn.smv $UNREAL
genbuf10f9unrealy.smv $UNREAL
genbuf7c2unrealn.smv $UNREAL
genbuf1c2unrealn.smv $UNREAL
genbuf14b3unrealy.smv $UNREAL
genbuf14c2unrealy.smv $UNREAL
genbuf4c2unrealy.smv $UNREAL
genbuf15b3unrealy.smv $UNREAL
genbuf11c2unrealn.smv $UNREAL
genbuf10c2unrealy.smv $UNREAL
genbuf7c3y.smv $REAL
genbuf10b3unrealy.smv $UNREAL
genbuf10f10y.smv $REAL
genbuf10f9unrealn.smv $UNREAL
genbuf6b3unrealn.smv $UNREAL
genbuf16f15unrealn.smv $UNREAL
genbuf16c3y.smv $REAL
genbuf1c2unrealy.smv $UNREAL
genbuf12c3y.smv $REAL
genbuf5b3unrealn.smv $UNREAL
genbuf5c2unrealn.smv $UNREAL
genbuf6f5unrealn.smv $UNREAL
genbuf14b4y.smv $REAL
genbuf13f13n.smv $REAL
genbuf6c2unrealy.smv $UNREAL
genbuf11c2unrealy.smv $UNREAL
genbuf11f11n.smv $REAL
genbuf6f6y.smv $REAL
genbuf2c2unrealn.smv $UNREAL
genbuf12f12y.smv $REAL
genbuf14c3y.smv $REAL
genbuf3f3unrealy.smv $UNREAL
genbuf16c2unrealy.smv $UNREAL
genbuf9f9y.smv $REAL
genbuf1b3unrealy.smv $UNREAL
genbuf8b3unrealy.smv $UNREAL
genbuf7b3unrealy.smv $UNREAL
amba3c4unrealn.smv $UNREAL
genbuf12b4n.smv $REAL
genbuf12f11unrealn.smv $UNREAL
genbuf3b3unrealy.smv $UNREAL
genbuf9b3unrealn.smv $UNREAL
genbuf6b4n.smv $REAL
genbuf13f12unrealy.smv $UNREAL
genbuf15b3unrealn.smv $UNREAL
genbuf16f16n.smv $REAL
genbuf7f7n.smv $REAL
genbuf16b3unrealn.smv $UNREAL
genbuf6c3n.smv $REAL
genbuf13c3n.smv $REAL
genbuf3c3y.smv $REAL
genbuf6c2unrealn.smv $UNREAL
genbuf9f9n.smv $REAL
genbuf1b4n.smv $REAL
cycle_sched_5.smv $REAL
add8n.smv $REAL
add10y.smv $REAL
gb_s2_r2_1_UNREAL.smv $UNREAL
cycle_sched_8.smv $REAL
cycle_sched_6.smv $REAL
cycle_sched_9.smv $REAL
add8y.smv $REAL
cycle_sched_7.smv $REAL
unrealizable.smv $UNREAL
cycle_sched_10.smv $REAL
unrealizable.smv $UNREAL
add16n.smv $REAL
unrealizable.smv $UNREAL
unreal.smv $UNREAL
amba5c5y.smv $REAL
load_full_2_5_UNREAL.smv $UNREAL
add10n.smv $REAL
add12y.smv $REAL
add14y.smv $REAL
add16y.smv $REAL
add12n.smv $REAL
    )

CALL_SYNTH_TOOL="./runf.sh $@ "
TIMESTAMP=`date +%s`
RES_TXT_FILE="${DIR}tests/results_fwd_${TIMESTAMP}.txt"
RES_DIR="${DIR}tests/results_fwd_${TIMESTAMP}/"
mkdir -p "${DIR}tests/"
mkdir -p ${RES_DIR}

ulimit -m ${MEMORY_LIMIT} -v ${MEMORY_LIMIT} -t ${TIME_LIMIT}
for element in $(seq 0 2 $((${#FILES[@]} - 1)))
do
     file_name=${FILES[$element]}
     infile_path=${BM_DIR}${file_name}
     outfile_path=${RES_DIR}${file_name}_synth.aag
     correct_real=${FILES[$element+1]}
     echo "Synthesizing ${file_name} ..."
     echo "=====================  $file_name =====================" 1>> $RES_TXT_FILE

     #------------------------------------------------------------------------------
     # BEGIN execution of synthesis tool
     echo " Running the synthesizer ... "
     ${GNU_TIME} --output=${RES_TXT_FILE} -a -f "Synthesis time: %e sec (Real time) / %U sec (User CPU time)" ${CALL_SYNTH_TOOL} $infile_path >> ${RES_TXT_FILE}
     #"-o" $outfile_path "-ot" >> ${RES_TXT_FILE}
     exit_code=$?
     echo "  Done running the synthesizer. "
     # END execution of synthesis tool

     if [[ $exit_code == 137 ]];
     then
         echo "  Timeout!"
         echo "Timeout: 1" 1>> $RES_TXT_FILE
         continue
     else
         echo "Timeout: 0" 1>> $RES_TXT_FILE
     fi

     if [[ $exit_code != $REAL && $exit_code != $UNREAL ]];
     then
         echo "  Strange exit code: $exit_code (crash or out-of-memory)!"
         echo "Crash or out-of-mem: 1 (Exit code: $exit_code)" 1>> $RES_TXT_FILE
         continue
     else
         echo "Crash or out-of-mem: 0" 1>> $RES_TXT_FILE
     fi

     #------------------------------------------------------------------------------
     # BEGIN analyze realizability verdict
     if [[ $exit_code == $REAL && $correct_real == $UNREAL ]];
     then
         echo "  ERROR: Tool reported 'realizable' for an unrealizable spec!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
         echo "Realizability correct: 0 (tool reported 'realizable' instead of 'unrealizable')" 1>> $RES_TXT_FILE
         continue
     fi
     if [[ $exit_code == $UNREAL && $correct_real == $REAL ]];
     then
         echo "  ERROR: Tool reported 'unrealizable' for a realizable spec!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
         echo "Realizability correct: 0 (tool reported 'unrealizable' instead of 'realizable')" 1>> $RES_TXT_FILE
         continue
     fi
     if [[ $exit_code == $UNREAL ]];
     then
         echo "  The spec has been correctly identified as 'unrealizable'."
         echo "Realizability correct: 1 (unrealizable)" 1>> $RES_TXT_FILE
     else
         echo "  The spec has been correctly identified as 'realizable'."
         echo "Realizability correct: 1 (realizable)" 1>> $RES_TXT_FILE
#
#         # END analyze realizability verdict
#
#         #------------------------------------------------------------------------------
#         # BEGIN syntactic check
#         echo " Checking the synthesis result syntactically ... "
#         if [ -f $outfile_path ];
#         then
#             echo "  Output file has been created."
#             python $SYNT_CHECKER $infile_path $outfile_path
#             exit_code=$?
#             if [[ $exit_code == 0 ]];
#             then
#               echo "  Output file is OK syntactically."
#               echo "Output file OK: 1" 1>> $RES_TXT_FILE
#             else
#               echo "  Output file is NOT OK syntactically."
#               echo "Output file OK: 0" 1>> $RES_TXT_FILE
#             fi
#         else
#             echo "  Output file has NOT been created!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
#             echo "Output file OK: 0 (no output file created)" 1>> $RES_TXT_FILE
#             continue
#         fi
#         # TODO: perform syntactic check here.
#         # END syntactic check
#
#         #------------------------------------------------------------------------------
#         # BEGIN model checking
#         echo -n " Model checking the synthesis result ... "
#         ${GNU_TIME} --output=${RES_TXT_FILE} -a -f "Model-checking time: %e sec (Real time) / %U sec (User CPU time)" $MODEL_CHECKER $outfile_path > /dev/null 2>&1
#         check_res=$?
#         echo " done. "
#         if [[ $check_res == 20 ]];
#         then
#             echo "  Model-checking was successful."
#             echo "Model-checking: 1" 1>> $RES_TXT_FILE
#         else
#             echo "  Model-checking the resulting circuit failed!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
#             echo "Model-checking: 0 (exit code: $check_res)" 1>> $RES_TXT_FILE
#         fi
#         # END end checking
#
#         #------------------------------------------------------------------------------
         # BEGIN determining circuit size
#         aig_header_in=$(head -n 1 $infile_path)
#         aig_header_out=$(head -n 1 $outfile_path)
#         echo "Raw AIGER input size: $aig_header_in" 1>> $RES_TXT_FILE
#         echo "Raw AIGER output size: $aig_header_out" 1>> $RES_TXT_FILE
#         # START ABC optimization to compare sizes
#         ../aiger/aigtoaig $outfile_path "${outfile_path}.aig"
#         ../ABC/abc -c "read_aiger ${outfile_path}.aig; strash; refactor; rewrite; dfraig; scleanup; rewrite; dfraig; write_aiger -s ${outfile_path}_opt.aig"
#         ../aiger/aigtoaig "${outfile_path}_opt.aig" "${outfile_path}_opt.aag"
#         aig_header_opt=$(head -n 1 "${outfile_path}_opt.aag")
#         echo "Raw AIGER opt size: $aig_header_opt" 1>> $RES_TXT_FILE
#         # END determining circuit size           
     fi
done
