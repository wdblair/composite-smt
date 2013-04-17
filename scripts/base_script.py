#!/usr/bin/python

import threading, sys, subprocess, Queue

class Z3(threading.Thread):
    def __init__(self, smt, q):
        threading.Thread.__init__(self)
        self.smt = smt
        self.q = q
    def run(self):
        process = subprocess.Popen(['z3', '-smt', self.smt], stdout=subprocess.PIPE)
        out, err = process.communicate()
        if out.split('\n')[0] == 'unknown':
            return None        
        try:
            self.q.put_nowait(out)
            print (out, "z3")
        except Queue.Full:
            #it loss
            pass
            
class Yices(threading.Thread):
    def __init__(self, smt, q):
        threading.Thread.__init__(self)
        self.smt = smt
        self.q = q
    def run(self):
        process = subprocess.Popen(['yices-smt', self.smt], stdout=subprocess.PIPE)
        out, err = process.communicate()
        if out.split('\n')[0] == 'unknown':
            return None
        try:
            self.q.put_nowait(out)
            print (out, 'yices')
        except Queue.Full:
            #it loss
            pass


file = sys.argv[1]
q = Queue.Queue(1)

z3 = Z3(file, q)
yices = Yices(file, q)
z3.start()
yices.start()