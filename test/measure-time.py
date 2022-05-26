import json
import subprocess
from subprocess import PIPE, DEVNULL, TimeoutExpired
import sys
import time
import matplotlib.pyplot as plt
import numpy as np

if __name__ == '__main__':
    if len(sys.argv) < 5:
        print("Usage: python3.9 main.py <plot title> top step name1:exec1 name2:exec2 name3:exec3...")
        exit(1)
    title = sys.argv[1]
    top = int(sys.argv[2])
    step = int(sys.argv[3])

    times = []
    ress = []
    labels = []
    # xs = np.arange(top, step=step)
    #
    # for x in sys.argv[4:]:
    #     label,filename = x.split(":")
    #     labels.append(label)
    #     print("\n", label)
    #
    #     times1 = []
    #     res1 = []
    #     for i in xs:
    #         ns0 = time.time_ns()
    #
    #         cmd = filename + " " + str(i)
    #         timeout = 20
    #         try:
    #             pipe = subprocess.run(cmd, shell=True, stdout=PIPE, stderr=DEVNULL, timeout=timeout)
    #             if pipe.returncode == 0:
    #                 res = pipe.stdout.decode('utf-8').strip()
    #                 res1.append(res)
    #                 ns1 = time.time_ns()
    #                 ns = ((ns1 - ns0) // 1000) / 1000000
    #                 times1.append(ns)
    #                 print(str(i) + ":", ns, "s")
    #                 print(str(i) + ":", res)
    #             else:
    #                 print(label, "crashed, skipping the rest of the benchmarks. Error:", pipe.stdout)
    #                 break
    #
    #         except TimeoutExpired:
    #             print(str(i) + ": timeout")
    #             times1.append(timeout)
    #             break
    #
    #     f = open(filename + "-times.json", 'w')
    #     json.dump(times1, f)
    #     f.close()
    #
    #     times.append(times1)
    #     ress.append(res1)
    #
    # for res1 in ress:
    #     for res2 in ress:
    #         for x,y in zip(res1, res2):
    #             assert x == y

    fhs = open("Triples-malonzo-times.json", 'r')
    haskell = json.load(fhs)
    fhs.close()
    labels.append("haskell")
    times.append(haskell)

    fscheme = open("chez --script Triples.so-times.json", 'r')
    scheme = json.load(fscheme)
    fscheme.close()
    labels.append("scheme")
    times.append(scheme)

    # fhvm = open("Triples-times.json", 'r')
    # hvm = json.load(fhvm)
    # labels.append("hvm")
    # times.append(hvm)
    #
    # bohm = [0, 0.3, 1.32, 13.85, 101.07]
    # labels.append("bohm")
    # times.append(bohm)

    xs = np.arange(300, step=10)

    plt.figure(figsize=(6, 8))
    plt.title(title)
    for label1,times1 in zip(labels, times):
        times1 = [t ** (1/3) for t in times1]
        plt.plot(xs[0:len(times1)], times1, label=label1)
    plt.legend()
    plt.xlabel("n")
    plt.ylabel("cube root of running time (s)")
    plt.show()
