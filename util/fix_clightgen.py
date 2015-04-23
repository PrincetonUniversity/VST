import os
import sys
import re

# For each conflicting identifier, replace its positive with the next largest seen positive
#  that isn't on the excluded list
# Remove all lines which match the above regex from all files, and replace with the new bindings

def getFullPaths(files):
    # Get full path to file
    cwd = os.getcwd()
    fullpaths = map(lambda x : cwd + '/' + x, files)
    filteredpaths = []
    for p in fullpaths:
        if not os.path.exists(p):
            print("File " + p + " doesn't exist, skipping")
        else:
            print("Using file " + p)
            filteredpaths.append(p)
    return filteredpaths

def readVFile(f):
    # At the same time, find other positives that are used, and add them to an excluded list
    regex = re.compile("^Definition (\S+) : ident := (\d+)%positive.$")
    # Need to make sure this is a non-greedy .* (otherwise it will match one of the digits)
    numberregex = re.compile(".*?(\d+)%positive.*")
    with open(f) as h:
        text = h.read()
    splitText = text.splitlines()
    restOfFile = []
    excluded = set()
    # Build up a map of identifier to positive for each file and one for all files
    varBindings = {}
    for line in splitText:
        m = regex.match(line)
        if m:
            varBindings[m.group(1)] = int(m.group(2))
        else:
            restOfFile.append(line)
            m2 = numberregex.match(line)
            if m2:
                excluded.add(m2.group(1))
    dictEntry = {
        "bindings" : varBindings,
        "restOfFile" : restOfFile
    }
    return dictEntry, excluded

def readVFiles(files):
    fileDict = {}
    excludedSet = set()
    identifierSet = set()
    for f in files:
        dictEntry, excluded = readVFile(f)
        fileDict[f] = dictEntry
        excludedSet |= excluded
        identifierSet |= set(dictEntry["bindings"].keys())
    parsedFilesDict = {
        "files" : fileDict,
        "excluded" : excludedSet,
        "identifiers" : identifierSet
    }
    return parsedFilesDict

# Find all identifiers which are mapped to different positives across the different files
def findConflicts(parsed):
    conflicts = set()
    fileDict = parsed["files"]
    for ident in parsed["identifiers"]:
        seen = False
        val= -1
        for f in fileDict:
            entry = fileDict[f]
            bindings = entry["bindings"]
            if ident in bindings:
                if seen == True and val != bindings[ident]:
                    conflicts.add(ident)
                    break
                else:
                    seen = True
                    val = bindings[ident]
    return conflicts

def fixConflicts(parsed, conflicts):
    # Find the smallest val which is not used
    highest = 0
    fileDict = parsed["files"]
    # Need to check for the highest positive used by either a
    # conflicting identifier or a number in the excluded list
    for k in fileDict:
        dictEntry = fileDict[k]
        bindings = dictEntry["bindings"]
        for b in bindings:
            highest = max(bindings[b], highest)
    for v in parsed["excluded"]:
        highest = max(int(v), highest)
    highest += 1
    for ident in conflicts:
        for k in fileDict:
            dictEntry = fileDict[k]
            bindings = dictEntry["bindings"]
            if ident in bindings:
                bindings[ident] = highest
        # increment to the next available identifier
        highest += 1
        while str(highest) in parsed["excluded"]:
            highest += 1

def writeFixedFiles(parsed):
    files = parsed["files"]
    for f in files:
        dictEntry = files[f]
        bindings = dictEntry["bindings"]
        restOfFile = dictEntry["restOfFile"]
        newDefinitions = []
        for ident in bindings:
            string = "Definition {} : ident := {}%positive.".format(ident, bindings[ident])
            newDefinitions.append(string)
        newDefinitions.sort()
        entireFile = restOfFile[0:4] + newDefinitions + restOfFile[4:]
        fileText = '\n'.join(entireFile)
        with open(f, "w") as h:
            h.write(fileText)

# files : list of filenames
def fix_clightgen(files):
    filtered = getFullPaths(files)
    # Read in all .v files listed
    # Parse for lines of the form "Definition \S : ident := \d+%positive."
    parsedFiles = readVFiles(filtered)
    conflictingIdentifiers = findConflicts(parsedFiles)
    fixConflicts(parsedFiles, conflictingIdentifiers)
    writeFixedFiles(parsedFiles)

if __name__ == "__main__":
    files = sys.argv[1:]
    fix_clightgen(files)
