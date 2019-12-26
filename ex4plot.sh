gnuplot -e "
set ylabel "Accessible node, %";
set y2label "Num Query average";
set y2tics;
set y2range [0:1]
plot "plot.txt" using 1:2 axis x1y1 with linespoint lc rgb "light-cyan" title "accessible, %", "plot.txt" using 1:3:xtic(1) axis x1y2 with linespoint lc rgb "light-green" title "Query average";
set xlabel "Time";
replot;
pause -1
"
