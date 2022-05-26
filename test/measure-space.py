import json
import subprocess
import sys
import matplotlib.pyplot as plt
import numpy as np
from subprocess import PIPE, DEVNULL, TimeoutExpired

if __name__ == '__main__':
    if len(sys.argv) < 5:
        print("Usage: python3.9 main.py <plot title> top step name1:exec1 name2:exec2 name3:exec3...")
        exit(1)
    title = sys.argv[1]
    top = int(sys.argv[2])
    step = int(sys.argv[3])

    mems = []
    ress = []
    labels = []
    for x in sys.argv[4:]:
        label,filename = x.split(":")
        labels.append(label)
        print("\n", label)

        mems1 = []
        res1 = []
        xs = np.arange(top, step=step)
        for i in xs:
            cmd = 'gtime -o /dev/stdout -f "%M" ' + filename + ' ' + str(i)

            try:
                pipe = subprocess.run(cmd, shell=True, stdout=PIPE, stderr=DEVNULL, timeout=10)
                if pipe.returncode == 0:
                    lines = pipe.stdout.decode('utf-8').splitlines()
                    res = lines[0]
                    memstr = lines[1]
                    mem = float(memstr) / 1000000  # GB
                    print(i, "mem:", mem, "GB")
                    print(str(i) + ":", res)
                    mems1.append(mem)
                    res1.append(res)
                else:
                    print(label, "crashed, skipping the rest of the benchmarks. Error:", pipe.stdout)
                    break

            except TimeoutExpired:
                print(str(i) + ": timeout")
                break


        f = open(filename + "-mems.json", 'w')
        json.dump(mems1, f)

        mems.append(mems1)
        ress.append(res1)

    for res1 in ress:
        for res2 in ress:
            for x,y in zip(res1, res2):
                assert x == y

    f.close()
    plt.figure(figsize=(6, 8))
    plt.title(title)
    for label1,mems1 in zip(labels, mems):
        plt.plot(mems1, label=label1)
    plt.legend()
    plt.xlabel("n")
    plt.ylabel("Memory usage (GB)")
    plt.show()
