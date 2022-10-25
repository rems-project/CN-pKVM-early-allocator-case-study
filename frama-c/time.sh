sum=0
count=5

for value in $(seq 1 $count);
do
    make clean
    make generated.c
    start=`date +%s.%N`
    frama-c -wp -wp-rte -wp-timeout 1 generated.c
    end=`date +%s.%N`
    runtime=$( echo "$end - $start" | bc -l )
    sum=$( echo "$sum + $runtime" | bc -l )
done

echo "$sum / $count" | bc -l
