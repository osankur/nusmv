 #!/bin/bash          
DEFAULTDIR="/home/sankur/work/ulb/syntcomp/bench-syntcomp14/"
if [ -f $1 ]
then
  FILE=$1
else
  FILE=$DEFAULTDIR$1
fi
printf "read_model -i $FILE\n
flatten_hierarchy\n
encode_variables\n
dynamic_var_ordering -e sift\n
build_model\n
check_realizable -f\n
quit" > /tmp/sauce
./NuSMV -source /tmp/sauce
exit $?
