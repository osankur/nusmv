#!/bin/bash          
DEFAULTDIR="/home/sankur/work/ulb/syntcomp/bench-syntcomp14/"
if [ -f $1 ]
then
  FILE=$1
else
  FILE=$DEFAULTDIR$1
fi
COMMAND="read_model -i $FILE\n
flatten_hierarchy\n
encode_variables\n
dynamic_var_ordering -e sift\n
build_model\n
check_realizable -b\n
quit"
echo -e $COMMAND | ./NuSMV -int 
echo ""
