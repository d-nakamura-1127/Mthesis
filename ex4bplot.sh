#!/bin/sh

gnuplot -e "
set ylabel 'accessible';
plot 'plot.txt' using 1:2 with linespoint lc rgb 'red' title '|M|=5,not group', 'plot.txt' using 1:4 with linespoint lc rgb 'dark-red' title '|M|=5,group', 'plot.txt' using 1:6 with linespoint lc rgb 'red' title '|M|=10,not group', 'plot.txt' using 1:8 with linespoint lc rgb 'dark-red' title '|M|=10,group', 'plot.txt' using 1:10 with linespoint lc rgb 'red' title '|M|=15,not group', 'plot.txt' using 1:12 with linespoint lc rgb 'dark-red' title '|M|=15,group', 'plot.txt' using 1:14 with linespoint lc rgb 'red' title '|M|=20,not group', 'plot.txt' using 1:16 with linespoint lc rgb 'dark-red' title '|M|=20,group', 'plot.txt' using 1:18 with linespoint lc rgb 'red' title '|M|=25,not group', 'plot.txt' using 1:4 with linespoint lc rgb 'dark-red' title '|M|=5,group';
set xlabel 'Time';
set xrange [0:60];
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"
