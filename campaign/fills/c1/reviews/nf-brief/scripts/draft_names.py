import sys, re
draft, probe = sys.argv[1], sys.argv[2]
d = open(draft, encoding="utf-8").read()
names = set()
for m in re.finditer(r'`([^`\n]+)`', d):
    t = m.group(1).strip()
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'₀-₉]*", t) and ('.' in t or '_' in t or t[0].isupper()):
        names.add(t)
probe_names = set(re.findall(r'#check @(\S+)', open(probe, encoding="utf-8").read()))
short = {p.split('.')[-1]: p for p in probe_names}
for n in sorted(names):
    full = [p for p in probe_names if p == n or p.endswith('.' + n) or p == 'Turing.' + n]
    print(f"{'IN ' if full else '-- '} {n}" + (f"  ({full[0]})" if full else ""))
