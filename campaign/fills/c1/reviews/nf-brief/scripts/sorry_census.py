import sys, re
root, order_file = sys.argv[1:3]
tot = 0; nmod = 0
for l in open(order_file):
    m = l.strip()
    if not m: continue
    p = f"{root}/{m}.lean"
    try: src = open(p, encoding="utf-8").read()
    except FileNotFoundError: continue
    # strip block comments and line comments (nested /- -/ handled crudely)
    out = []; depth = 0; i = 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if depth and src.startswith("-/", i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = len(src) if j < 0 else j; continue
        out.append(src[i]); i += 1
    code = "".join(out)
    n = len(re.findall(r'\bsorry\b', code))
    if n:
        nmod += 1; tot += n; print(f"{m}: {n}")
print("TOTAL sorry tokens", tot, "in", nmod, "modules")
