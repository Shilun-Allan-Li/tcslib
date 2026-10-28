import sys, os, re
root, order_file, roots_file, target = sys.argv[1:5]
overlay_extra = {"TCSlib.Complexity.ClassNP.NDNormalForm": ["TCSlib.Complexity.TuringMachine.Build.NDHost", "TCSlib.Complexity.TuringMachine.Build.StepBlock"]}
mods = {}
for dp, dn, fn in os.walk(os.path.join(root, "TCSlib")):
    for f in fn:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            m = os.path.relpath(p, root)[:-5].replace("/", ".")
            imps = []
            for line in open(p, encoding="utf-8"):
                mm = re.match(r'^import\s+(\S+)', line)
                if mm: imps.append(mm.group(1))
            mods[m] = imps + overlay_extra.get(m, [])
# also TCSlib.lean root itself not included in walk; fine
def tc(m, memo={}):
    if m in memo: return memo[m]
    memo[m] = set()
    s = set()
    for i in mods.get(m, []):
        if i.startswith("TCSlib"):
            s.add(i); s |= tc(i)
    memo[m] = s
    return s
down = {m for m in mods if target in tc(m)}
closure = set(down) | {target}
for m in list(closure):
    closure |= {i for i in tc(m)}
order = [l.strip().replace("/", ".") for l in open(order_file) if l.strip()]
print("order list entries:", len(order), "unique:", len(set(order)))
print("computed set (downstream of target + their closures + target):", len(closure))
print("in order not computed:", sorted(set(order) - closure))
print("computed not in order:", sorted(closure - set(order)))
print("downstream of target:", sorted(down))
pos = {m: i for i, m in enumerate(order)}
bad = [(m, i) for m in order for i in mods.get(m, []) if i in pos and pos[i] > pos[m]]
print("topological violations:", bad)
mathlib_roots = set()
for m in order:
    for i in mods.get(m, []):
        if not i.startswith("TCSlib"): mathlib_roots.add(i)
listed = {l.strip() for l in open(roots_file) if l.strip()}
print("Mathlib roots computed:", len(mathlib_roots), "listed:", len(listed), "equal:", mathlib_roots == listed)
print("diff computed-listed:", sorted(mathlib_roots - listed), "listed-computed:", sorted(listed - mathlib_roots))
print("position of target:", pos.get(target))
