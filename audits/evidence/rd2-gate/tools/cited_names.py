"""List the backticked identifiers cited in the given files' comments/docstrings that look like
Lean declaration names (dotted or snake/camel identifiers), one per line, with their file."""
import re, sys
tok = re.compile(r'`([A-Za-z_][A-Za-z0-9_.\'ᵢ₀-₉]*)`')
seen = {}
for f in sys.argv[1:]:
    text = open(f, encoding='utf-8').read()
    # comments only: docstrings and module docs and line comments
    for m in re.finditer(r'/-[-!]?(.*?)-/', text, re.S):
        for t in tok.findall(m.group(1)):
            if t in seen: continue
            if '.' in t or '_' in t or re.match(r'^[a-z]+[A-Z]', t) or re.match(r'^[A-Z][a-z]+[A-Z]', t):
                seen[t] = f.split('/')[-1]
for t, f in seen.items():
    print(f"{t}\t{f}")
