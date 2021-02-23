#!/bin/bash
#
# Build a report using the files produced by run_bench 
# Usage: build_report.sh n
#
# n: timeout (in seconds)


# grep "^pref" file.txt:  match string having pref as prefix


export LC_NUMERIC="en_US.UTF-8"  # needed to recognize decimal numbers with dot

# set TIMEOUT
if [  -z "$1" ]; then
   cmdName=$(basename $0)
   echo "Usage: $cmdName n" 
   echo "where n is the timeout in seconds used in the experiments, for example:"
   echo "$cmdName 600"
   exit
fi

TIMEOUT="$1"

timings_intuitR="intuitR_${TIMEOUT}_"       
timings_intuit="intuit_${TIMEOUT}_"         



# sum the numbers in $1
# result: sum_timings
function sum(){
    timings=$1
    sum_timings=0
    for k in $timings
    do
	# echo $k
	sum_timings=$(bc <<< "$sum_timings + $k" )
    done
    }

# analyze the performances  of a prover on a prover
# $1: the name of the problem (prefix of the name)
# $2: prover
# $3: prover name
function analyze_problem_prover(){
    local problem="$1"
    local prover="$2"
    local prover_name="$3"
    local timings=$( grep "^$problem" $prover  | cut -d',' -f2 )
    local valid_timings=$(grep  -v '-' <<< $timings )
    count_solved=$( wc -l <<< $valid_timings  )
    count_timeout=$( grep '-' <<< $timings | wc -l)
    sum "$valid_timings"
    if (( $count_timeout > 0 ))
    then
	timeout="## TIMEOUT ##"
    else
	timeout=""
    fi
    printf "%s %d (%.3f) %s\n"  "$prover_name" $count_solved  $sum_timings  "$timeout"
}   


# analyze the performances on  a problem
# $1: the name of the problem (prefix of the name)
function analyze_problem(){
    local problem="$1"
    local timings=$( grep "^$problem" $timings_intuitR  | cut -d',' -f2 )
    local count_formulas=$(wc -l  <<< $timings)
    echo "#### ${problem%_} ($count_formulas) ####"
    # {problem%_}: remove last _ 
    analyze_problem_prover "$problem" $timings_intuitR     "intuitR    "
    if [ -f  $timings_intuit ]; then
	analyze_problem_prover "$problem" $timings_intuit      "intuit     "
    fi	
}
    

    
#### MAIN ####




problems="EC LCL SYJ1 \
 SYJ201 SYJ202  SYJ203 SYJ204 SYJ205 SYJ206 \
 SYJ207 SYJ208  SYJ209 SYJ210 SYJ211 SYJ212 \
 SYN cross jm_bind jm_cross jm_lift \
 join lift map0 map1 map2 mapf\
 negEC negportia_ negportiav2 \
 nishimura2 nishimura_ \
 portia rights unsec"




for probl in $problems
do
   analyze_problem "$probl"
done

