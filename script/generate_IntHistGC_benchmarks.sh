
## SETTINGS

INTUIT_REST=intuitR    # command to launch intuitR  

BENCHMARKS_DIR=../Benchmarks # intuitR/intuit benchmarks
INTHISTGC_DIR=Benchmarks_intHistGC      #dir. for IntHistGC Benchmarks 

# check if intuitR is defined
if   ! command -v $INTUIT_REST  &> /dev/null
then
    echo "$INTUIT_REST: command not found"
    exit 
fi    


mkdir -p $INTHISTGC_DIR


testFiles=$(ls $BENCHMARKS_DIR/*p)

echo "Generating IntHistGC benchmarks..."
for file in $testFiles
do
    outFile=$INTHISTGC_DIR/$(basename $file)
    ## echo "$outFile"
    $INTUIT_REST -IntHistGC "$file"  > "$outFile"
done
    
echo "Created directory INTHISTGC_DIR"
