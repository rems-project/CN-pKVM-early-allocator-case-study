sum=0
count=5

for value in $(seq 1 $count);
do
    make clean
    make rc-project.toml
    start=`date +%s.%N`
    refinedc check -I ../original early_alloc.c
    end=`date +%s.%N`
    runtime=$( echo "$end - $start" | bc -l )
    sum=$( echo "$sum + $runtime" | bc -l )
done

echo "$sum / $count" | bc -l
