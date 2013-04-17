#!/usr/bin/python

import threading, sys, subprocess

class Z3(threading.Thread):
    def __init__(self, smt):
        self.smt = smt
    def run(self):
        process = subprocess.Popen(['z3', '-smt', self.smt], stdout=subprocess.PIPE)
        out, err = process.communicate()
        print out


file = sys.argv[1]
mutex = threading.Lock()


z3 = Z3(file)
z3.start()