#!/bin/sh

gnuplot -e "
set style fill solid border lc rgb 'black';
set boxwidth 1;
plot 'plot.txt' using ($0*4+0):2 with boxes lw 2 lc rgb 'light-cyan' title 'Nbc=0', 'plot.txt' using ($0*4+1):3:xtic(1) with boxes lw 2 lc rgb 'light-green' title 'Nbc=1', 'plot.txt' using ($0*4+2):4 with boxes lw 2 lc rgb 'light-pink' title 'Nbc=10';
set xlabel 'Nbc';
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"