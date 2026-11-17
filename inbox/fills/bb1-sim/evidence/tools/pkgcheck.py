# pkgcheck.py <clone>: every package present in <clone>/.lake/packages must match lake-manifest.json's URL and rev;
# packages of the manifest that are not present are listed ABSENT. Written for bb1-sim-statements (lead).
# Copied unchanged from bb1-sim-statements (evidence/tools/pkgcheck.py) for bb1-sim (lead).
import json, os, subprocess, sys
root = sys.argv[1]
man = json.load(open(os.path.join(root, 'lake-manifest.json')))
ok = True
for p in man['packages']:
    d = os.path.join(root, '.lake', 'packages', p['name'])
    if not os.path.isdir(d):
        print('ABSENT', p['name']); continue
    url = subprocess.run(['git', '-C', d, 'remote', 'get-url', 'origin'], capture_output=True, text=True).stdout.strip()
    rev = subprocess.run(['git', '-C', d, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    m = url == p['url'] and rev == p['rev']
    ok &= m
    print('MATCH' if m else 'MISMATCH', p['name'], url, rev, '' if m else f"(manifest {p['url']} {p['rev']})")
print('PACKAGES-CHECK', 'PASS (every present package matches its manifest URL and revision)' if ok else 'FAIL')
sys.exit(0 if ok else 1)
