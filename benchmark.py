#!/usr/bin/env python3
import sys
import re
from statistics import mean, stdev

# Process a line from Coq output:
# If the line contains a lemma name, return it as a str
# If the line contains a timing info, extract the part like 0.159u and return as a float
def process_line(s):
    m = re.search(r"[0-9.]+u", s)
    if m:
        return float(m.group()[:-1])
    else:
        return s[:-1]

# Process each line of the given file, and return a list
def readfile(filename):
    f = open(filename)
    lines = f.readlines()
    f.close()
    return [process_line(line) for line in lines]

def add_entry(dict, key, value):
    if(key in dict):
        dict[key].append(value)
    else:
        dict[key] = [value]

def work(filename):
    global res
    l = readfile(filename)
    buf = []
    for e in l:
        if isinstance(e, str):
            if len(buf) > 0:
                add_entry(res, lemma, buf)
            buf = []
            lemma = e
        else:
            buf.append(e)
    if len(buf) > 0:
        add_entry(res, lemma, buf)

global res
res = {}
for i in range (1, len(sys.argv)):
    work(sys.argv[i])
# Transpose lists for each lemma
res = {key : list(map(list, zip(*value))) for (key, value) in res.items()}
# print(res)

def print_one(l):
    print("mean: ", mean(l))
    print("sd: ", stdev(l))
    print("min: ", min(l))
    print("max: ", max(l))
    print()

def print_lemma(lemma, ll):
    print(lemma)
    list(map(print_one, ll))

list(map(lambda kv : print_lemma(*kv), res.items()))