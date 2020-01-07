#!/bin/sh

gnuplot -e "
set ylabel 'Num Query Average';
plot 'plot.txt' using 1:3 with linespoint lc rgb 'red' title 'not group', 'plot2.txt' using 1:3 with linespoint lc rgb 'blue' title 'group';
set xlabel 'Time';
set xrange [0:60];
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"