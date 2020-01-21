#!/bin/sh

n=5
gnuplot -e "
set ylabel 'Num TABLE REQ';
plot 'plot-ex4.txt' using 1:$n+4*0 with linespoint title '|M|=0', 'plot-ex4.txt' using 1:$n+4*1 with linespoint title '|M|=5', 'plot-ex4.txt' using 1:$n+4*2 with linespoint title '|M|=10', 'plot-ex4.txt' using 1:$n+4*3 with linespoint title '|M|=15', 'plot-ex4.txt' using 1:$n+4*4 with linespoint title '|M|=20', 'plot-ex4.txt' using 1:$n+4*5 with linespoint title '|M|=25', 'plot-ex4.txt' using 1:$n+4*6 with linespoint title '|M|=30', 'plot-ex4.txt' using 1:$n+4*7 with linespoint title '|M|=35', 'plot-ex4.txt' using 1:$n+4*8 with linespoint title '|M|=40', 'plot-ex4.txt' using 1:$n+4*9 with linespoint title '|M|=45', 'plot-ex4.txt' using 1:$n+4*10 with linespoint title '|M|=50';
set xlabel 'Time';
set xrange [30:60];
set key right bottom;
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"
