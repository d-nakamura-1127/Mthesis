#!/bin/sh

gnuplot -e "
set ylabel 'Num TABLE REQ';
plot 'plot_NUMTREQ.txt' using 1:2 with linespoint lc rgb 'red' title 'not group', 'plot2_NUMTREQ.txt' using 1:2 with linespoint lc rgb 'blue' title 'group';
set xlabel 'Time';
set xrange [30:60];
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"
