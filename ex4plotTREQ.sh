#!/bin/sh

gnuplot -e "
set ylabel 'Num TABLE REQ';
plot 'plot_NUMTREQ.txt' using 1:2 with linespoint lc rgb 'red' title '|M|=10,not group', 'plot_NUMTREQ.txt' using 1:3 with linespoint lc rgb 'dark-red' title '|M|=10,group', 'plot2_NUMTREQ.txt' using 1:2 with linespoint lc rgb 'blue' title '|M|=50,not group', 'plot2_NUMTREQ.txt' using 1:3 with linespoint lc rgb 'navy' title '|M|=50,group';
set xlabel 'Time';
set xrange [30:60];
set yrange [0:400];
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"