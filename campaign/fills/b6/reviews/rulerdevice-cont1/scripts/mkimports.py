"""Import graph of a git tree's TCSlib modules as JSON {module: [imported TCSlib modules]}.
usage: python3 -I mkimports.py <repo> <commit> <out.json>"""
import json, re, subprocess, sys
repo, rev, out = sys.argv[1:4]
files = subprocess.run(['git', '-C', repo, 'ls-tree', '-r', '--name-only', rev, '--', 'TCSlib', 'TCSlib.lean'], capture_output=True, text=True).stdout.split()
g = {}
for f in files:
    if not f.endswith('.lean'): continue
    src = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
    imps = [m.group(1).replace('.', '/') for m in re.finditer(r'^import\s+(TCSlib\S*)', src, re.M)]
    g[f[:-5]] = imps
json.dump(g, open(out, 'w'), indent=0, sort_keys=True)
print(out.rsplit('/', 1)[1], len(g), 'modules')
