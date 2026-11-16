import json, subprocess, sys, os
root = sys.argv[1]
m = json.load(open(os.path.join(root, "lake-manifest.json")))
ok = True; absent = []
for p in m["packages"]:
    d = os.path.join(root, ".lake/packages", p["name"])
    if not os.path.isdir(d):
        absent.append(p["name"]); print(f"ABSENT {p['name']}"); continue
    url = subprocess.run(["git", "-C", d, "remote", "get-url", "origin"], capture_output=True, text=True).stdout.strip()
    rev = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    good = url == p["url"] and rev == p["rev"]
    ok &= good
    print(f"{'MATCH' if good else 'MISMATCH'} {p['name']} url={url} rev={rev} manifest_url={p['url']} manifest_rev={p['rev']}")
print(f"RESULT: {'PASS' if ok else 'FAIL'}: present packages match the manifest; absent: {', '.join(absent) or 'none'}")
