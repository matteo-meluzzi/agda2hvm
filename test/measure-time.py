import json
import os
import sys
import time
import matplotlib.pyplot as plt
import numpy as np

if __name__ == '__main__':
    if len(sys.argv) < 4:
        print("Usage: python3.9 main.py top step name1:exec1 name2:exec2 name3:exec3...")
        exit(1)
    top = int(sys.argv[1])
    step = int(sys.argv[2])

    times = []
    ress = []
    labels = []
    for x in sys.argv[3:]:
        label,filename = x.split(":")
        labels.append(label)

        times1 = []
        res1 = []
        xs = np.arange(top, step=step)
        for i in xs:
            ns0 = time.time_ns()
            res = os.popen("./" + filename + " " + str(i)).read()
            res1.append(res)
            ns1 = time.time_ns()
            ns = ((ns1 - ns0) // 1000) / 1000000
            times1.append(ns)
            print(i, ":", ns)
        print(times1, "s")
        f = open(filename + "-times.json", 'w')
        json.dump(times1, f)

        times.append(times1)
        ress.append(res1)

    for res1 in ress:
        for res2 in ress:
            assert res1 == res2

    f.close()
    plt.figure(figsize=(4.66, 7.11))

    for label1,times1 in zip(labels, times):
        plt.plot(times1, label=label1)

    plt.legend()
    plt.xlabel("n")
    plt.ylabel("running time (s)")
    plt.show()
