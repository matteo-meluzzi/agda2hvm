import json
import sys
import time
import matplotlib.pyplot as plt
import numpy as np
from subprocess import Popen, PIPE, DEVNULL

# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    if len(sys.argv) < 4:
        print("Usage: python3.9 main.py top step name1:exec1 name2:exec2 name3:exec3...")
        exit(1)
    top = int(sys.argv[1])
    step = int(sys.argv[2])

    mems = []
    ress = []
    labels = []
    for x in sys.argv[3:]:
        label,filename = x.split(":")
        labels.append(label)

        mems1 = []
        res1 = []
        xs = np.arange(top, step=step)
        for i in xs:
            ns0 = time.time_ns()
            cmd = 'gtime -o /dev/stdout -f "%M" ./' + filename + ' ' + str(i)
            pipe = Popen(cmd, shell=True, stdin=PIPE, stdout=PIPE, stderr=DEVNULL, close_fds=True)
            res = pipe.stdout.readline().decode("utf-8").strip()
            memstr = pipe.stdout.readline().decode("utf-8").strip()
            mem = float(memstr)/1000 # MB
            print(i, "mem:", mem, "MB")

            res1.append(res)
            mems1.append(mem)

        print(mems1, "MB")
        f = open(filename + "-mems.json", 'w')
        json.dump(mems1, f)

        mems.append(mems1)
        ress.append(res1)

    for res1 in ress:
        for res2 in ress:
            assert res1 == res2

    f.close()
    plt.figure(figsize=(4.66, 7.11))

    for label1,mems1 in zip(labels, mems):
        plt.plot(mems1, label=label1)

    plt.legend()
    plt.xlabel("n")
    plt.ylabel("Memory usage (MB)")
    plt.show()
