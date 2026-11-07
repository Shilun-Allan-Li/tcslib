import os, re, sys
root = sys.argv[1]; dirs = sys.argv[2].split(','); wanted = sys.argv[3].split(',')
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |)*(?:noncomputable )?(def|structure|class|abbrev|theorem|lemma|inductive|instance)\s+([^\s(:{\[]+)')
found = {}
for d in dirs:
    for dp, _, fs in os.walk(os.path.join(root, d)):
        for f in fs:
            if not f.endswith('.lean'): continue
            p = os.path.join(dp, f); ns = []
            for i, line in enumerate(open(p, encoding='utf-8'), 1):
                m = re.match(r'^namespace\s+(\S+)', line)
                if m: ns.append(m.group(1)); continue
                m = re.match(r'^end\s+(\S+)', line)
                if m and ns and ns[-1] == m.group(1): ns.pop(); continue
                m = decl.match(line)
                if m and not line.startswith('private'):
                    full = '.'.join(ns + [m.group(2)])
                    found.setdefault(full, []).append(f"{os.path.relpath(p, root)}:{i} {m.group(1)}")
for w in wanted:
    hits = [(k, v) for k, v in found.items() if k == w or k.endswith('.' + w)]
    print(f"{w}: " + ('; '.join(f"{k} @ {v[0]}" for k, v in hits) if hits else 'MISSING'))
