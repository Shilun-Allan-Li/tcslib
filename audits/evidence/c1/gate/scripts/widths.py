import sys
bad = 0
for p in sys.argv[1:]:
    for i, l in enumerate(open(p, encoding="utf-8").read().split("\n"), 1):
        if len(l) > 100:
            print(f"{p}:{i}: {len(l)} chars"); bad += 1
print("over-100 lines:", bad)
