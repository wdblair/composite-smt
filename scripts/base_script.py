#!/usr/bin/python

import threading, sys, subprocess, Queue

class Z3(threading.Thread):
    def __init__(self, smt, q, killq):
        threading.Thread.__init__(self)
        self.smt = smt
        self.q = q
        self.killq = killq
    def run(self):
        process = subprocess.Popen(['z3', '-smt', self.smt], stdout=subprocess.PIPE)
        self.put_nowait(process)
        out, err = process.communicate()
        killp = process
        while killp is process:
            killp = self.killq.get()
        killp.kill()
        if out.split('\n')[0] == 'unknown':
            return None        
        try:
            self.q.put_nowait(out)
            print (out, "z3")
        except Queue.Full:
            #it loss
            pass
            
class Yices(threading.Thread):
    def __init__(self, smt, q, killq):
        threading.Thread.__init__(self)
        self.smt = smt
        self.q = q
        self.killq = killq
    def run(self):
        process = subprocess.Popen(['yices-smt', self.smt], stdout=subprocess.PIPE)
        self.put_nowait(process)
        out, err = process.communicate()
        killp = process
        while killp is process:
            killp = self.killq.get()
        killp.kill()
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
killq = Queue.Queue(2)
z3 = Z3(file, q, killq)
yices = Yices(file, q, killq)
z3.start()
yices.start()