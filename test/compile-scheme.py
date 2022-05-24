import sys
import os

filename = sys.argv[1]
name = filename.split(".")[0]

os.system('agda2scheme --lazy ' + filename)
os.system('echo \'(display (main (delay (string->number (car (command-line-arguments)))))) (display "\\n")\' >> ' + name + '.ss')
os.system('echo \'(compile-file "' + name + '.ss")\' | chez -q')
os.system('chez --script ' + name + '.so 0')
