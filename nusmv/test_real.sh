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
TIME_LIMIT=500
# Memory limit in kB:
MEMORY_LIMIT=2000000

# Maybe change the following line to point to GNU time:
GNU_TIME="time"
MODEL_CHECKER="$DIR/../blimc/blimc"
SYNT_CHECKER="$DIR/../aiger/syntactic_checker.py"

# The directory where the benchmarks are located:
BM_DIR="/home/sankur/work/ulb/syntcomp/bench-syntcomp14/"

REAL=10
UNREAL=20

# The benchmarks to be used.
# The files have to be located in ${BM_DIR}.
FILES=(
unrealizable.smv $UNREAL
    )

CALL_SYNTH_TOOL="./runf.sh $@ "
TIMESTAMP=`date +%s`
RES_TXT_FILE="${DIR}tests/results_${TIMESTAMP}.txt"
RES_DIR="${DIR}tests/results_${TIMESTAMP}/"
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
