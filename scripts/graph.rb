#!/usr/bin/env ruby

if ARGV.size < 1
  STDERR.puts "Usage: graph.rb logic"
end

logic = ARGV[0]

logfile = logic.downcase + ".log"

data = {z3: {}, yices: {}, both: {}, unknown: 0}

File.open(logfile, "r") do |log|
  search_unknown = false
  log.each_line do |file|
    file.chomp!
    if search_unknown and not file.empty?
      data[:unknown] += 1
    end
    
    if file =~ /^Unknown Files\:.*/
      search_unknown = true
    end
    
    if file =~ /.*::(yices|z3|both)::(\d+)/
      sym = $1.to_sym
      timeout = $2
      data[sym][timeout] ||= 0
      data[sym][timeout] += 1
    end
  end
end


#xtics = "z3 0, yices 1, both 2, unknown 3"

xtics = data.each_with_index.map { |res, i|
  "#{res[0]} #{i}"
}.join(", ")

min = 0
width = 1

headlines = "Solver 1s 5s 10s 30s 1m 2m 5m 10m\n"

data_pts = data.each_with_index.map { |res, i|
  name = res[0]
  if name.to_s == 'unknown'
    "#{name} #{res[1]}"
  else
    times = ["1", "5", "10", "30", "60", "120", "300", "600"].map { |t|
      res[1][t] || 0
    }.join(" ")
    "#{name} #{times}"
  end
}.join("\n")

#Prepare all the gnuplot commands
commands = ["set terminal svg",
            "set xrange [-1:#{data.size}]",
            "set title \"#{logfile}\"",
            "set grid",
            "set auto y",
            "set boxwidth #{width}",
            "set xlabel \"Solvers\"",
            "set ylabel \"Tests Solved Within Timeout\"",
            "set tics out nomirror",
            "set style data histogram",
            "set style histogram cluster gap 2",
            "set style fill solid 0.5",
            "set xtic rotate by -75",
            "set output \"#{logfile}.svg\"",
            "plot '-' using 2:xtic(1) ti col, \
                  '' u 3 ti col, \
                  '' u 4 ti col, \
                  '' u 5 ti col, \
                  '' u 6 ti col, \
                  '' u 7 ti col, \
                  '' u 8 ti col, \
                  '' u 9 ti col"
].join("\n")

gnu = IO.popen("gnuplot", "r+")

gnu.puts commands

8.times do 
  gnu.puts headlines
  gnu.puts data_pts
  
  gnu.puts "e"
end

gnu.close_write
