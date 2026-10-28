import sys
root = sys.argv[1]
checks = [
 ("TCSlib/Complexity/ClassNP/NDNormalForm.lean", [6,7,20,21,22,30,31,43,45,46,66,77,78,84,86,88]),
 ("TCSlib/Complexity/TuringMachine/Build/NDHost.lean", [571,1705,1706,1707,1721,1760,1809,1951,1999]),
 ("TCSlib/Complexity/ClassNP/NTIME.lean", [96,104]),
 ("TCSlib/Complexity/TuringMachine/NDCodes.lean", [99]),
 ("TCSlib/Complexity/TuringMachine/Build/StepBlock.lean", [134,135,136,137,138,142,146,149,153,163,198,199]),
 ("TCSlib/Complexity/TuringMachine/Nondeterministic.lean", [474,488]),
]
for f, ls in checks:
    lines = open(f"{root}/{f}", encoding="utf-8").read().split("\n")
    print(f"## {f} ({len(lines)-1 if lines[-1]=='' else len(lines)} lines)")
    for n in ls:
        print(f"{n:5d}: {lines[n-1]}")
