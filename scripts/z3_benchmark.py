#!/usr/bin/python
import time
import os, sys, subprocess

test_dir = sys.argv[1]
devnull = open('/dev/null', 'w')
error_log = open(sys.argv[2], 'w')

time_start = time.time()
for root, dirs, files in os.walk(test_dir):
    for file in files:
        sub_start = time.time()
        subprocess.call(['z3', '-smt', root+'/'+file], stdout=devnull, stderr=error_log)
        sub_time = time.time() - sub_start
        print "Time for file {0} is {1}".format(file, sub_time)
time_stop = time.time()
time_elapsed = time_stop - time_start
print "Total Time for benchmark: {0}".format(time_elapsed)
devnull.close()
error_log.close()