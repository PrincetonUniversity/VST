# Takes the last proof body of given file, and creates files where this proof body
# is cut to length 0, 1, 2, ... lines, admitting the rest with an axiom, and
# Qed'ing it.

import sys

if len(sys.argv) != 2:
  print "Usage: 1 argument: Name of file to be split"
  sys.exit(1)

# sys.argv[0] is script name

filename = sys.argv[1]

print "Filename is", filename
if filename[-1] != 'v' or filename[-2] != '.':
  print "Expected .v file!"
  sys.exit(1)

with open(filename) as f:
  content = f.readlines()
# remove whitespace characters at the end of each line
content = [x.rstrip() for x in content]
# remove subgoal focus, does not work if bullets are used, or "all:" or "1:" etc
content = [x.replace("{", "").replace("}", "") for x in content]

lastProof = len(content) - 1
while content[lastProof] != "Proof." and lastProof > 0:
  lastProof -= 1

if lastProof == 0:
  print "Error: No 'Proof.' found"
  sys.exit(1)

n = len(content)-lastProof

def makeFilename(i, ext):
  return filename[:-2] + "_proofbodylength" + i + ext

for i in range(n):
  newname = makeFilename(str(i), '.v')
  print "Creating file", newname
  with open(newname, 'w') as fout:
    fout.write('Axiom EverythingIsTrue: forall (P: Prop), P.\n')
    for j in range(lastProof+i):
      fout.write(content[j])
      fout.write('\n')
    fout.write('all: apply EverythingIsTrue.\n')
    fout.write('Time Qed.\n')

print "Created", n, "files."
print "Test them with"
print "for i in {0..%d}; do make %s; done"%(n-1, makeFilename("$i", ".vo"))

