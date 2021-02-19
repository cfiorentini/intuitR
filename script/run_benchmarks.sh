# Run all the benchmarcks with intuitR and intuit (if defined)
# 
# Usage:  run_benchmarks m
#
# where n is the timoeout in seconds used in the experiments

# GLOBAL SETTINGS

INTUIT_REST=intuitR    # command to launch intuitR  
INTUIT=intuit          # command to launch intuit (by Claessen & Rosen)  


INTUIT_TEST_DIR=../Benchmarks




# set TIMEOUT
if [  -z "$1" ]; then
   cmdName=$(basename $0)
   echo "Usage: $cmdName n" 
   echo "where n is the timeout in seconds, for example:"
   echo "$cmdName 600"
   exit
fi

TIMEOUT="$1"
echo "Timeout: $TIMEOUT secs."





# if necessary, compile  Run.hs
if [ ! -f Run ]; then
    echo "Compiling Run.sh..."
    # cabal install --lib split
    ghc --make Run.hs -o Run || exit 
fi
# run 

echo -n ">>> START: "
date  # print start time


# check if intuitR is defined
if   ! command -v $INTUIT_REST  &> /dev/null
then
    echo "$INTUIT_REST: command not found"
    exit 
fi    

# run benchmarks with intuitR
./Run $INTUIT_TEST_DIR   $TIMEOUT $INTUIT_REST   "intuitR"

# check if intuit is defined
if   ! command -v $INTUIT  &> /dev/null
then
    echo "$INTUIT: command not found"
    exit 
fi    

# run benchmarks
./Run  $INTUIT_TEST_DIR   $TIMEOUT $INTUIT   "intuit"


echo -n ">>> END: "
date # print end time
