gnuplot -e "
set style fill solid border lc rgb 'black';
set boxwidth 1;
set ylabel 'Accessible node, %;
plot 'plot.txt' using ($0*4+0):2 with boxes lw 2 lc rgb 'light-cyan' title 'Nbc=0', 'plot.txt' using ($0*4+1):3 with boxes lw 2 lc rgb 'light-green' title 'Nbc=1', 'plot.txt' using ($0*4+2):4 with boxes lw 2 lc rgb 'light-red' title 'Nbc=10';
set xlabel 'Time';
replot;
pause -1
"
