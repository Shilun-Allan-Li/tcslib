import json, subprocess, os, sys
m=json.load(open('lake-manifest.json'))
ok=True; absent=[]
for p in m['packages']:
    d=os.path.join('.lake/packages',p['name'])
    if not os.path.isdir(d): absent.append(p['name']); print('ABSENT',p['name']); continue
    url=subprocess.run(['git','-C',d,'remote','get-url','origin'],capture_output=True,text=True).stdout.strip()
    rev=subprocess.run(['git','-C',d,'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    good = url==p['url'] and rev==p['rev']
    ok &= good
    print('OK' if good else 'MISMATCH', p['name'], f"url={url}", f"rev={rev}")
print('RESULT:', ('PASS: every present package matches the manifest; absent: '+', '.join(absent)) if ok else 'FAIL')
