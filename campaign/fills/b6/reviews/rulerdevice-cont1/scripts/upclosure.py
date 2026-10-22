import json, sys
g = json.load(open(sys.argv[1])); roots = sys.argv[2:]
seen = set(); st = list(roots)
while st:
    x = st.pop()
    for y in g.get(x, []):
        if y not in seen: seen.add(y); st.append(y)
print('\n'.join(sorted(seen)))
