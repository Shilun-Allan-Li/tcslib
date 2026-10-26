import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import history_lib as H
import df4lib
base, head = sys.argv[1], sys.argv[2]
files = subprocess.run(['git', 'diff', '--name-only', base, head, '--', '*.lean'], capture_output=True, text=True, check=True).stdout.split()
for path in files:
    ta, tb = H.load(base, path), H.load(head, path)
    if ta is None or tb is None: print(path, 'new or deleted'); continue
    (A, visA, collA), (B, visB, collB) = H.model(ta), H.model(tb)
    coll = collA | collB; out = []
    for n in sorted(set(A) | set(B)):
        if n not in coll: continue
        a, b = A.get(n), B.get(n)
        if a == b: continue
        seen = (a is None or n in visA) and (b is None or n in visB)
        out.append((n, 'visible' if seen else 'INVISIBLE'))
    print(path, 'collided names:', len(coll), 'changed among them:', out)
