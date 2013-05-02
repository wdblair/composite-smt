#!/usr/bin/env ruby

logic = ARGV[0]

results = {}

File.open(logic+".log", "r") do |f|
  current_file = nil
  f.each_line do |line|
    if line =~ /(.*?).smt:(Z3|yices):(\d+.\d+):(\d+.\d+)/
      file = $1 + ".smt"
      current_file = file
      solver = $2
      user = $3.to_f
      real = $4.to_f
      
      time = [user, real].min

      results[current_file] ||= {}
      results[current_file][solver] = time
    end

    if line =~ /(z3|yices):(z3|yices)/
      #I'll determine the winner
      #user_winner = $1
      #real_winner = $2
    end
  end
end

points = []

results.each do |key, stats|
  points << "#{stats["Z3"]} #{stats["yices"]}"
end

data = points.join("\n")

commands = <<-EOS
set terminal svg font "arial,10" size 550, 500
set output '#{logic}.svg'
set border 3 front linetype -1 linewidth 1.000
set logscale xy
set grid nopolar
unset key
set title "#{logic}: Performance Test"
set xlabel "Z3"
set ylabel "Yices 2"
set yrange [0.01 : 35.0 ]
set xrange [0.01 : 35.0 ]
plot "-" using 1:2 with points, x with lines
EOS

gnu = IO.popen("gnuplot", "r+")

gnu.puts commands

gnu.puts data
gnu.puts "e"

gnu.close_write
