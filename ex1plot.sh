#!/bin/sh

gnuplot -e "
plot 'plot.txt' using 1:2 with linespoint lw 2 title 'Nbc=0', 'plot.txt' using 1:3:xtic(1) with linespoint lw 2 title 'Nbc=1', 'plot.txt' using 1:4 with linespoint lw 2 title 'Nbc=10';
set xlabel 'Nbc';
set ylabel 'Average Time';
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"
