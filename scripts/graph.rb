#!/usr/bin/env ruby

# Graphing Script:
# Collect samples from each logic and put each in a histogram
# in a bar graph. Modify the commands variable for title and 
# such.

if ARGV.size < 1
  STDERR.puts "Usage: graph.rb logic1 logic2 logic3"
end

graph_title = "Comparing Yices 2.0 with Z3"

logics = ARGV

def process logic

  logfile = logic.downcase + ".log"

  data = {z3: {}, yices: {}, both: {}, unknown: {}}

  sum = 0
  File.open(logfile, "r") do |log|
    search_unknown = false
    log.each_line do |file|
      file.chomp!
      if search_unknown and not file.empty?
        data[:unknown]["600"] ||= 0
        data[:unknown]["600"] += 1
        sum += 1
      end
      
      if file =~ /^Unknown Files\:.*/
        search_unknown = true
      end
      
      if file =~ /.*::(yices|z3|both)::(\d+)/
        sym = $1.to_sym
        timeout = $2
        data[sym][timeout] ||= 0
        data[sym][timeout] += 1
        sum += 1
      end
    end
  end

  headlines = "Solver 1s 5s 10s 30s 1m 2m 5m 10m\n"

  data_pts = data.each_with_index.map { |res, i|
    name = res[0]
    times = ["1", "5", "10", "30", "60", "120", "300", "600"].map { |t|
      res[1][t] ||= 0
      res[1][t] = (res[1][t].to_f / sum.to_f) * 100.0
    }.join(" ")
    "#{name} #{times}"
  }.join("\n")

  headlines + data_pts
end

information = logics.map do |l| process (l) end

min = 0
width = 1
init = false

plots = logics.map { |l|
  title = if not init then "t col" else "notitle" end
  
  label = "newhistogram \'#{l}\' lt 1, '-' using 2:xtic(1) #{title}"
  cols =  (3..9).map {  |i|
    "'' u #{i} #{title}"
  }.join(", ")
  init = true
  label + ", " + cols
}.join(", ")

commands = <<-EOS
set terminal svg background rgb "white" font "arial,10" size 960, 400
set output 'yices.svg'
set border 3 front linetype -1 linewidth 1.000
set boxwidth 0.8 absolute
set style fill   solid 1.00 noborder
set grid nopolar
set grid noxtics nomxtics ytics nomytics noztics nomztics \
 nox2tics nomx2tics noy2tics nomy2tics nocbtics nomcbtics
set grid layerdefault   linetype 0 linewidth 1.000,  linetype 0 linewidth 1.000
set key bmargin center horizontal Left reverse noenhanced autotitles columnhead nobox
set style histogram rowstacked title  offset character 2, 0.25, 0
set style data histograms
set xtics border in scale 0,0 nomirror rotate by -45  offset character 0, 0, 0 autojustify
set xtics  norangelimit font ",8"
set xtics   ()
set ytics border in scale 0,0 mirror norotate  offset character 0, 0, 0 autojustify
set ztics border in scale 0,0 nomirror norotate  offset character 0, 0, 0 autojustify
set cbtics border in scale 0,0 mirror norotate  offset character 0, 0, 0 autojustify
set rtics axis in scale 0,0 nomirror norotate  offset character 0, 0, 0 autojustify
set title "#{graph_title}"
set xlabel "Logics"
set xlabel  offset character 0, -2, 0 font "" textcolor lt -1 norotate
set ylabel "% of Formulas Solved Within Timeout"
set yrange [ 0.00000 : 100. ] noreverse nowriteback
plot #{plots}
EOS

gnu = IO.popen("gnuplot", "r+")

gnu.puts commands

information.each do |info|
  8.times do
    gnu.puts info
    gnu.puts "e"
  end
end

gnu.close_write
