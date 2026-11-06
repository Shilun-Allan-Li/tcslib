import os, re, sys, collections
root = sys.argv[1]
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private |protected |noncomputable |partial |unsafe )*)(def|structure|class|abbrev|theorem|lemma|inductive|opaque|axiom)\s+([^\s(:{\[]+)')
seen = collections.defaultdict(list)
for dp, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); ns = []
        for i, line in enumerate(open(p, encoding='utf-8', errors='replace'), 1):
            m = re.match(r'^namespace\s+(\S+)', line)
            if m: ns.append(m.group(1)); continue
            m = re.match(r'^end\s+(\S+)\s*$', line)
            if m and ns and ns[-1] == m.group(1): ns.pop(); continue
            m = decl.match(line)
            if m and 'private' not in m.group(1):
                name = m.group(3)
                full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns + [name])
                seen[full].append(f"{os.path.relpath(p, root)}:{i}")
d = {k: v for k, v in seen.items() if len(set(x.split(':')[0] for x in v)) > 1}
for k in sorted(d): print(k, '|', ' ; '.join(d[k]))
print(f"# {len(d)} full names declared in more than one file", file=sys.stderr)
