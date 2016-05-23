 #!/bin/bash          
DEFAULTDIR="~/ulb/syntcomp/nusmv/nusmv/examples/synth/"
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
build_model -m Iwls95CP\n
time\n
check_eventually_invar -n $2\n
time\n
" > /tmp/sauce
./NuSMV -source /tmp/sauce
exit $?
