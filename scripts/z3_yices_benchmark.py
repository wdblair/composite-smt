#!/usr/bin/env python
import os, sys, subprocess

test_dir = sys.argv[1]
log_name = sys.argv[2]
total_y_usr_wins = 0
total_z_usr_wins = 0
total_y_ela_wins = 0
total_z_ela_wins = 0
result_file = open(log_name+'.log', 'w')
stdout_file = open(log_name+'.stdout', 'w')
stderr_file = open(log_name+'.stderr', 'w')

for root, dirs, files in os.walk(test_dir):
    for file in files:
        if !file.endswith(".smt"):
            continue
        rep
        usr, sys, chusr, chsys, ela = os.times()
        subprocess.call(['timeout', '30', 'z3', '-smt', root+'/'+file], stdout=stdout_file, stderr=stderr_file)
        usr, sys, chusr2, chsys, ela2 = os.times()
        subprocess.call(['timeout', '30', 'yices-smt', root+'/'+file], stdout=stdout_file, stderr=stderr_file)
        usr, sys, chusr3, chsys, ela3 = os.times()
        z3usr = chusr2 - chusr
#        z3ela = ela2 - ela
        yicesusr = chusr3 - chusr2
#        yicesela = ela3 - ela2
#        usr_winner = 'z3'
#        if yicesusr < z3usr:
#            usr_winner = 'yices'
#            total_y_usr_wins += 1
#        else:
#            total_z_usr_wins += 1
#        ela_winner = 'z3'
#        if yicesela < z3ela:
#            ela_winner = 'yices'
#            total_y_ela_wins += 1
#        else:
#            total_z_ela_wins += 1
#        result_file.write("Time for file {0} with Z3 is usr:{1}, real: {2}\n".format(file, z3usr, z3ela))
#        result_file.write("Time for file {0} with yices is usr:{1}, real: {2}\n".format(file, yicesusr, yicesela))
#        result_file.write("User time winner is {0}, real time winner is {1}\n".format(usr_winner, ela_winner))
        result_file.write("{0}:{1}:{2}\n".format(root+'/'+file, z3usr, yicesusr))

#result_file.write('''Total Wins
#Yices Usr: {0}, Real: {1}
#Z3 Usr: {2}, Real: {3}\n'''.format(total_y_usr_wins, total_y_ela_wins, total_z_usr_wins, total_z_ela_wins))

result_file.close()
stdout_file.close()
stderr_file.close()
