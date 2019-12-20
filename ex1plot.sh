gnuplot -e "
set boxwidth 0.5 relative;
set style fill solid border lc rgb "black";
plot "plot.txt" using ($0*4+0):2 with boxes lw 2 lc rgb "light-cyan"  title "Q=0", "plot.txt" using ($0*4+1):3:xtic(1) with boxes lw 2 lc rgb "light-green" title "Q=1","plot.txt" using ($0*4+2):4 with boxes lw 2 lc rgb "light-pink"  title "Q=10" ;
set xlabel "Number of beacon";
set ylabel "Accessible node, %"
replot;
pause -1
"
