# This is a sample Python script.

# Press ⌃R to execute it or replace it with your code.
# Press Double ⇧ to search everywhere for classes, files, tool windows, actions, and settings.
import getopt
import json
import os
import sys
import time
import matplotlib.pyplot as plt
import numpy as np

# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    if len(sys.argv) != 5:
        print("Usage: python3.9 benchmark.py exec1 exec2 top step")
        exit(1)
    filename = sys.argv[1]
    filename2 = sys.argv[2]
    top = int(sys.argv[3])
    step = int(sys.argv[4])

    times1 = []
    xs = np.arange(top, step=step)
    for i in xs:
        ns0 = time.time_ns()
        os.system("./" + filename + " " + str(i))
        ns1 = time.time_ns()
        ns = ((ns1 - ns0) // 1000) / 1000000
        times1.append(ns)
        print(i, ":", ns)
    print(times1, "s")
    f = open("results1.json", 'w')
    json.dump(times1, f)

    times2 = []
    for i in xs:
        ns0 = time.time_ns()
        os.system("./" + filename2 + " " + str(i))
        ns1 = time.time_ns()
        ns = ((ns1 - ns0) // 1000) / 1000000
        times2.append(ns)
        print(i, ":", ns)
    print(times2, "s")
    f = open("results2.json", 'w')
    json.dump(times2, f)

    f.close()
    plt.figure(figsize=(4.66, 7.11))
    plt.plot(times1, label='hvm')
    plt.plot(times2, label='haskell')
    plt.legend()
    # plt.xticks(range(len(times1)))
    plt.xlabel("n")
    plt.ylabel("running time (s)")
    plt.show()


# See PyCharm help at https://www.jetbrains.com/help/pycharm/
