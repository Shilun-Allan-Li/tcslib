import json, subprocess, os, sys
m = json.load(open('lake-manifest.json'))
ok = True
for p in m['packages']:
    name = p['name']
    d = os.path.join('.lake/packages', name)
    if not os.path.isdir(d):
        print(f"ABSENT {name}")
        continue
    url = subprocess.run(['git','-C',d,'remote','get-url','origin'],capture_output=True,text=True).stdout.strip()
    rev = subprocess.run(['git','-C',d,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    good = (url == p['url'] and rev == p['rev'])
    ok &= good
    print(f"{'MATCH' if good else 'MISMATCH'} {name} url={url} rev={rev} manifest_url={p['url']} manifest_rev={p['rev']}")
print("RESULT: all present packages match the manifest" if ok else "RESULT: MISMATCH")
