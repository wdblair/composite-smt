#!/usr/bin/env ruby

logic = ARGV[0]

y_solver = ARGV[1]
x_solver = "Z3"

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
      if time == 0.0 then
	time = 0.005
      end
      results[current_file] ||= {}
      results[current_file][solver] = time
    end
  
    if line =~ /(.*?).smt:(\d+.\d+):(\d+.\d+)/
      current_file = $1
      results[current_file] ||= {}

      z3 = $2.to_f
      yices = $3.to_f

      if z3 == 0.0
	z3 = 0.005
      end

      if yices == 0.0
	yices = 0.005
      end

      results[current_file]["Z3"] = z3
      results[current_file]["yices"] = yices       
    end

    if line =~ /(z3|yices):(z3|yices)/
      # The winner isn't important
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
set terminal svg background rgb "white" font "arial,10" size 550, 500
set output '#{logic}.svg'
set border 3 front linetype -1 linewidth 1.000
set logscale xy
set grid nopolar
unset key
set title "#{logic}: Performance Test"
set xlabel "#{x_solver} (s)"
set ylabel "#{y_solver} (s)"
set yrange [0.005 : 35.0 ]
set xrange [0.005 : 35.0 ]
plot "-" using 1:2 with points linecolor rgb "black", x with lines
EOS

gnu = IO.popen("gnuplot", "r+")

gnu.puts commands

gnu.puts data
gnu.puts "e"

gnu.close_write
