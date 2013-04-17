#!/usr/bin/python

import threading, sys, subprocess

class Z3(threading.Thread):
    # def __init__(self):
    #     pass
    def run(self, smt):
        process = subprocess.Popen(['z3', '-smt', smt], stdout=subprocess.PIPE)
        out, err = process.communicate()
        print out


file = sys.argv[1]
mutex = threading.Lock()


z3 = Z3()
z3.start(file)