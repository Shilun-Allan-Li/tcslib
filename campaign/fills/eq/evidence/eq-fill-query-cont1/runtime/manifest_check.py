import json, subprocess, os, sys
m = json.load(open('lake-manifest.json'))
present = set(os.listdir('.lake/packages'))
ok = True; absent = []
for p in m['packages']:
    n = p['name']
    if n not in present:
        absent.append(n); print(f"ABSENT   {n} (manifest {p['url']} @ {p['rev']})"); continue
    d = f'.lake/packages/{n}'
    url = subprocess.run(['git','-C',d,'remote','get-url','origin'],capture_output=True,text=True).stdout.strip()
    rev = subprocess.run(['git','-C',d,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    good = (url == p['url'] and rev == p['rev'])
    ok &= good
    print(f"{'MATCH   ' if good else 'MISMATCH'} {n}: url={url} rev={rev} (manifest {p['url']} @ {p['rev']})")
extra = present - {p['name'] for p in m['packages']}
for e in sorted(extra): print(f"EXTRA    {e}"); ok = False
print(f"manifest check: {len(present)} present, all {'match' if ok else 'NOT matching'}; ABSENT (not cloned): {', '.join(absent) or 'none'}; {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
