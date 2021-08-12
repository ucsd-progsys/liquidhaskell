set datafile separator ','

# General config.
set autoscale
set bmargin 22    # For some reason using xticlabels adds tons of whitespaces at the end
set tics font ",4"

# Y (time) axis config
set ylabel "Time (seconds)"
set ytics font ",8"
set logscale y 10

# Chart shape
set style histogram clustered
set boxwidth 0.75 relative
set style fill transparent solid 0.5 noborder
set style histogram gap 0.25

# Grid
set style line 100 lt 1 lc rgb "grey" lw 0.5 # linestyle for the grid
set grid ls 100 # enable grid with specific linestyle

# X axis config
set xtics scale 0 rotate

set terminal svg enhanced size 8192,1024
set output 'perf.svg'
plot csv_2 using 2:xticlabels(1) with boxes lc rgb'red90' axis x1y1 title "after", \
     csv_3 using 2:xticlabels(1) with boxes lc rgb'blue90' axis x1y1 title "before", \
     '' u 0:($2+.1):(sprintf("%3.2f",$4-$2)) with labels rotate left font ",4" notitle
