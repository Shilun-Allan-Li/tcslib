import os, re, sys, json
root = sys.argv[1]
mods = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            m = os.path.relpath(p, root)[:-5]
            imps = []
            with open(p, encoding='utf-8') as fh:
                for line in fh:
                    s = line.strip()
                    mm = re.match(r'^import\s+(\S+)', s)
                    if mm:
                        name = mm.group(1)
                        if name.startswith('TCSlib'):
                            imps.append(name.replace('.', '/'))
            mods[m] = imps
json.dump(mods, open(sys.argv[2], 'w'))
print(len(mods))
