import json, subprocess, os, sys
m = json.load(open('lake-manifest.json'))
bad = 0
for p in m['packages']:
    d = os.path.join('.lake/packages', p['name'])
    if not os.path.isdir(d):
        print(f"ABSENT {p['name']}"); continue
    url = subprocess.run(['git','-C',d,'remote','get-url','origin'],capture_output=True,text=True).stdout.strip()
    rev = subprocess.run(['git','-C',d,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    ok = url == p['url'] and rev == p['rev']
    bad += not ok
    print(f"{'OK' if ok else 'MISMATCH'} {p['name']} {url} {rev}")
print(f"package check: {'PASS' if bad==0 else 'FAIL'} ({bad} mismatches)")
