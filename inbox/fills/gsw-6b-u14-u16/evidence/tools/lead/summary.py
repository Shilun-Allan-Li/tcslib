#!/usr/bin/env python3
"""C1 summary: one row per module of order.txt: the log that checked it last (the head sweep's for
the UNIT-DOWN modules, the bootstrap's for the rest, whose sources are unchanged), rc, errors in
both forms (`error:` and `error(`), `sorry` warnings, the SHA-256 of the source the check read
(recorded at launch) and whether it equals `git show HEAD:<path>`.
Usage: python3 -I summary.py <repo> <order.txt> <unit-down.txt> <boot-logs> <head-logs>"""
import sys, os, re, subprocess, hashlib
repo, order, down, boot, headl = sys.argv[1:6]
mods = [l.strip() for l in open(order) if l.strip()]
dn = {l.strip() for l in open(down) if l.strip()}
ERR = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
tot = bad = 0
print('module\tphase\trc\terrors\tsorry_warnings\tchecked_sha256\tHEAD_sha256\tbound')
for m in mods:
    d = headl if m in dn else boot
    p = os.path.join(d, m.replace('/', '__') + '.log')
    t = open(p).read()
    rc = re.findall(r'status=(\d+)', t)[-1]
    errs = len(ERR.findall(t))
    sw = t.count("declaration uses 'sorry'")
    cs = open(p + '.sha').read().strip()
    hs = hashlib.sha256(subprocess.run(['git', '-C', repo, 'show', f'HEAD:{m}.lean'], capture_output=True,
                                       check=True).stdout).hexdigest()
    ok = cs == hs and rc == '0' and errs == 0
    bad += not ok; tot += 1
    print(f"{m}\t{'head' if m in dn else 'bootstrap'}\t{rc}\t{errs}\t{sw}\t{cs}\t{hs}\t{'yes' if cs == hs else 'NO'}")
print(f'# {tot} modules; rc 0, 0 errors and source bound to HEAD: {tot - bad}; otherwise: {bad}')
