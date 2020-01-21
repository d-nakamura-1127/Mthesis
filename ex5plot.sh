#!/bin/sh

n=5
gnuplot -e "
set ylabel 'Num TABLE REQ';
plot 'plotdata/plot25.txt' using 1:$n with linespoint lw 2 title '|M|=25, flare', 'plotdata/plot25.txt' using 1:$n+4 with linespoint lw 2 title '|M|=25, flare-ex';
set xlabel 'Time';
set xrange [30:60];
set xlabel font 'Arial,20';
set ylabel font 'Arial,20';
set key font 'Arial,15';
replot;
pause -1
"