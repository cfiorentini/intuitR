
## SETTINGS

INTUIT_REST=intuitR    # command to launch intuitR  

BENCHMARKS_DIR=../Benchmarks    # intuitR/intuit benchmarks
FCUBE_DIR=Benchmarks_fCube     #dir. for fCube Benchmarks


# check if intuitR is defined
if   ! command -v $INTUIT_REST  &> /dev/null
then
    echo "$INTUIT_REST: command not found"
    exit 
fi    


mkdir -p $FCUBE_DIR 


testFiles=$(ls $BENCHMARKS_DIR/*p)

echo "Generating fCube benchmarks..."
for file in $testFiles
do
    outFile=$FCUBE_DIR/$(basename $file)
    # echo "$outFile"
    $INTUIT_REST -fCube "$file"  > "$outFile"
done

echo "Created directory $FCUBE_DIR"
