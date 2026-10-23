#!/usr/bin/env python3
"""Parse the worker's bootstrap and final-sweep logs against the order list and the base sorry set.

usage: sweep.py ORDER BASE_SORRIES BOOTSTRAP_LOG SWEEP_LOG BASE_FILE HEAD_FILE
Reads data only; prints a report.
"""
import re, sys, collections

order_p, base_p, boot_p, sweep_p, basef, headf = sys.argv[1:7]
order = [l.strip() for l in open(order_p) if l.strip() and not l.startswith('#')]
print(f"order list: {len(order)} modules; CodeSimulator at {order.index('TCSlib/Complexity/TuringMachine/CodeSimulator') + 1}")

base = {}
for l in open(base_p):
    m = re.match(r'(\S+): (\d+): (.*)$', l.strip())
    if m:
        base['TCSlib/Complexity/' + m.group(1)] = int(m.group(2))
print(f"base sorry set: {sum(base.values())} entries in {len(base)} modules")

def parse(path):
    mods = collections.OrderedDict()
    cur = None
    for l in open(path, encoding='utf-8', errors='replace'):
        m = re.match(r'^=== (TCSlib/\S+) (start|end|OK|FAIL)\b', l)
        if m:
            name, ev = m.group(1), m.group(2)
            d = mods.setdefault(name, {'events': [], 'sorry': [], 'errors': 0})
            d['events'].append(ev)
            cur = name if ev == 'start' else None
            continue
        m = re.match(r'^(TCSlib/\S+)\.lean:(\d+):(\d+): (warning|error): (.*)$', l)
        if m:
            mod = m.group(1)
            d = mods.setdefault(mod, {'events': [], 'sorry': [], 'errors': 0})
            if m.group(4) == 'error':
                d['errors'] += 1
            elif "declaration uses 'sorry'" in m.group(5):
                d['sorry'].append(int(m.group(2)))
    return mods

boot = parse(boot_p)
sweep = parse(sweep_p)
print(f"bootstrap: {len(boot)} modules seen; sweep: {len(sweep)} modules seen")
bo = list(boot)
print("bootstrap order == order list prefix:", bo == order[:len(bo)], f"(bootstrap covers order 1..{len(bo)})")
so = list(sweep)
print("sweep order == order list 66..118:", so == order[65:], f"({len(so)} modules)")
print("bootstrap ∩ sweep:", [order.index(m) + 1 for m in bo if m in sweep])
missing = [m for m in order if m not in boot and m not in sweep]
print("never checked:", missing)
errs = {m: d['errors'] for m, d in list(boot.items()) + list(sweep.items()) if d['errors']}
print("errors:", errs)
notdone = [m for m, d in boot.items() if 'end' not in d['events'] and 'OK' not in d['events']]
print("bootstrap modules started but not ended:", notdone)
notok = [m for m, d in sweep.items() if 'OK' not in d['events']]
print("sweep modules without OK:", notok)

# census: per module, the last run's sorry count (sweep overrides bootstrap)
census = {}
for m in order:
    if m in sweep:
        census[m] = ('sweep', sweep[m]['sorry'])
    elif m in boot:
        census[m] = ('bootstrap', boot[m]['sorry'])
tot = sum(len(v[1]) for v in census.values())
print(f"census (sweep over bootstrap): {tot} sorry warnings in {sum(1 for v in census.values() if v[1])} modules")
for m, (src, lines) in census.items():
    b = base.get(m, 0)
    if len(lines) != b:
        print(f"  DIFF {m}: {src} {len(lines)} at {lines} vs base {b}")
for m in base:
    if m not in census:
        print(f"  base module not in census: {m}")
# bootstrap-only census vs base, for modules in both
print("modules run in both bootstrap and sweep, sorry lines:")
for m in bo:
    if m in sweep:
        print(f"  {m}: bootstrap {boot[m]['sorry']} sweep {sweep[m]['sorry']}")
cs = 'TCSlib/Complexity/TuringMachine/CodeSimulator'
print("CodeSimulator bootstrap sorry lines:", boot.get(cs, {}).get('sorry'))
for tag, f in (('base', basef), ('head', headf)):
    lines = open(f, encoding='utf-8').read().split('\n')
    for i, l in enumerate(lines, 1):
        if re.match(r'^\s*(private )?theorem (exists_canonGrammarStage|exists_uniformSimulator)\b', l):
            print(f"  {tag} {i}: {l.strip()[:80]}")
