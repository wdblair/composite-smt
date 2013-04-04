#!/usr/bin/env ruby

require 'find'
require 'open4'
require 'securerandom'

logic, sample_size = ARGV

logic_file = logic.downcase + ".log"

### Uniformly select k distinct samples from a population

def random_sample (population, k)
  sample = Array.new(k)
  population.each_with_index do |file, i|
    j = SecureRandom.random_number(i).to_i
    if j < k 
      sample[j] = file
    end
  end

  sample
end

class WrongSMTOutput < StandardError
   attr :smt_file
   def initialize(smt_file)
       @smt_file = smt_file
   end
end

### Is the formula unknown to a solver?

def unknown?(command, file)
  found = false
  res = false
  lines = []
  status = Open4::popen4(command) do |pid, stdin, stdout, stderr|
	stdout.each_line do |line|
		if /(unknown|timeout)/.match(line)
			res = true
			found = true
		elsif /(sat|unsat)/.match(line)
			res = false
			found = true
		end
		lines.unshift line
  	end
  end
   
  
  if status.exitstatus == 124
      res = true
      found = true
  end

  if !found
      STDERR.puts("Problem in #{file}")
      STDERR.puts(lines.join(""))
      raise WrongSMTOutput.new(file)
  end
  
  res
end

## Collect all the files

files = []

Find.find(logic) do |file|
  if not (file =~ /smt$/)
    next
  end
  
  if File.directory? file
    next
  end

  files.push file
end

### Take a sample
#
sample = random_sample(files, sample_size.to_i)

unknowns = sample

### Find the lower bound for each formula

timeouts = [1, 5, 10, 30, 60, 120, 300, 600]

log = File.open(logic_file, "a+")

timeouts.each do |t|
	unknowns.select! do |formula|
		begin
			z3_idk = unknown?("timeout #{t} ./z3 -smt #{formula}", formula)
			yices_idk = unknown?("timeout #{t} ./yices-smt #{formula}", formula)
		rescue WrongSMTOutput => e
			# STDERR.puts e.smt_file + "::"
			STDERR.puts e.inspect
		end	
		
		#Still unknown
		if z3_idk and yices_idk	
			true
		#Have a lower bound for this guy
                else
			solver = 
				if not(z3_idk or yices_idk) then 
					"both" 
				elsif z3_idk then
					"yices"
				else
					"z3"
				end


		        log.puts [formula, solver, t].join("::")	
			puts "Finished #{formula}"
			false
		end
	end
end

### Collect the output
log.puts "Unknown Files:"

unknowns.each do |file|
	log.puts file
end

log.close()
