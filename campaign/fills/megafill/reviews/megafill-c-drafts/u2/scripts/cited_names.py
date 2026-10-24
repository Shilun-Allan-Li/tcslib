import re, sys
draft, probe = sys.argv[1], sys.argv[2]
t = open(draft).read()
names = set()
for m in re.finditer(r"`([^`]+)`", t):
    s = m.group(1)
    for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀-₉]*", s):
        if "." in tok or "_" in tok or tok[0].isupper():
            names.add(tok)
pc = set(re.findall(r"^#check @(\S+)", open(probe).read(), re.M))
short = {p.split(".")[-1]: p for p in pc}
def covered(n):
    if n in pc or ("Turing." + n) in pc or ("Turing.StepBlock." + n) in pc: return True
    tail = n.split(".")[-1]
    return any(p.endswith("." + n) for p in pc)
for n in sorted(names):
    if not covered(n):
        print(n)
