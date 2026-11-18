import sys
for f in sys.argv[1:]:
    lines = open(f, encoding='utf-8').read().split('\n')
    mx = max(len(l) for l in lines)
    for i, l in enumerate(lines, 1):
        if len(l) > 100: print(f"{f}:{i}: {len(l)}")
    print(f"SIZE {f} lines={len(lines)-1 if lines[-1]=='' else len(lines)} maxwidth={mx}")
