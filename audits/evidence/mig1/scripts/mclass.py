import json, re, sys, collections
r = json.load(open(sys.argv[1]))
def machine_ex(c):
    # top-level ∃ whose binder list (up to the first ',') mentions a machine type
    if not c.startswith('∃'): return False
    depth = 0
    for j, ch in enumerate(c):
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif ch == ',' and depth == 0:
            b = c[:j]; break
    else:
        b = c
    return bool(re.search(r'\b(FinTM|MultiTapeTM|CodeTM|OracleTM|FinNDTM|OracleNDTM)\b', b))
c = collections.Counter(); rows = []
for o in r:
    if machine_ex(o['concl']):
        c[o['file']] += 1; rows.append(o)
for k, v in sorted(c.items()): print(v, k)
print(sum(c.values()))
json.dump(rows, open(sys.argv[2], 'w'), indent=0, ensure_ascii=False)
