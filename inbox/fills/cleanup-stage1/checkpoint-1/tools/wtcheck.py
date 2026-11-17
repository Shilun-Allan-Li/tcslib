#!/usr/bin/env python3
"""Incremental one-module checker for a worktree with its own TCSlib olean tree (cleanup-stage1).

python3 -I wtcheck.py --wt WORKTREE --tree OLEANS --target TCSlib/X/Y [--target ...] [--log DIR]

* Computes the TCSlib import closure of each target (parsing `import TCSlib...` lines), in
  dependency order.
* A module's stamp is sha256(its source, the stamps of its TCSlib imports).  The stamps of the
  check base are computed from the lead clone's sources (HEAD = the check tree 01cc6259...).
* For each module of the closure, in order: if OLEANS has the olean with the current stamp, skip;
  else, if the module's stamp equals its check-base stamp (its source and every upstream source
  are byte-identical to the check base) and the lead's bootstrap built it with rc 0, COPY the
  lead's olean (seeding, recorded in OLEANS/.seeded.tsv); else REBUILD it with
  `bash <wt>/scripts/lean_check_tree.sh` under the host-wide lock (<lead clone>/.lean.lock).
* Waits until the lead's bootstrap has built every unchanged upstream module (no duplicate builds).
* The targets themselves are always rebuilt (that is the check).  Raw logs go to --log.
Exit 1 at the first failing module.  Never runs lake.
"""
import argparse, fcntl, hashlib, json, os, re, shutil, subprocess, sys, time

LEAD = '/home/user/s1/tcslib'
LEAD_TREE = '/home/user/s1/oleans/lead'
BOOT = '/home/user/s1/evidence/build/bootstrap/results.jsonl'
ERR = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
IMP = re.compile(r'^import\s+(TCSlib[\w.]*)', re.M)

ap = argparse.ArgumentParser()
ap.add_argument('--wt', required=True)
ap.add_argument('--tree', required=True)
ap.add_argument('--target', action='append', required=True)
ap.add_argument('--log', default=None)
a = ap.parse_args()
log = a.log or os.path.join(a.tree, '.logs')
os.makedirs(log, exist_ok=True)
os.makedirs(os.path.join(a.tree, '.stamps'), exist_ok=True)


def imports(root, m):
    p = os.path.join(root, m + '.lean')
    if not os.path.exists(p):
        return None
    head = open(p, encoding='utf-8').read().split('\n/-!', 1)[0]
    return [x.replace('.', '/') for x in IMP.findall(head)]


def stamps(root, mods_order):
    st = {}
    for m in mods_order:
        src = open(os.path.join(root, m + '.lean'), 'rb').read()
        h = hashlib.sha256(src)
        for d in sorted(imports(root, m)):
            h.update(st.get(d, 'MISSING').encode())
        st[m] = h.hexdigest()
    return st


def closure(root, targets):
    order, seen = [], set()
    def go(m):
        if m in seen:
            return
        seen.add(m)
        for d in imports(root, m) or []:
            go(d)
        order.append(m)
    for t in targets:
        go(t)
    return order


order = closure(a.wt, a.target)
cur = stamps(a.wt, order)
base_order = [m for m in order if os.path.exists(os.path.join(LEAD, m + '.lean'))]
try:
    base = stamps(LEAD, closure(LEAD, base_order))
except Exception:
    base = {}
booted = set()
if os.path.exists(BOOT):
    for l in open(BOOT):
        r = json.loads(l)
        if r['rc'] == 0 and r['errors'] == 0 and r['error_lines'] == 0:
            booted.add(r['module'])
ORDER = set(l.strip() for l in open('/home/user/work/pack/outbox/fills/cleanup-stage1/order.txt'))
need = [m for m in order if m not in a.target and m in ORDER and base.get(m) == cur.get(m)]
waited = False
while True:
    miss = [m for m in need if m not in booted]
    if not miss:
        break
    if not waited:
        print(f'waiting for the lead bootstrap: {len(miss)} unchanged upstream modules not built yet '
              f'(first: {miss[0]})', flush=True)
        waited = True
    time.sleep(30)
    for l in open(BOOT):
        r = json.loads(l)
        if r['rc'] == 0 and r['errors'] == 0 and r['error_lines'] == 0:
            booted.add(r['module'])
leadhead = subprocess.run(['git', '-C', LEAD, 'rev-parse', 'HEAD^{tree}'],
                          capture_output=True, text=True).stdout.strip()
seedlog = open(os.path.join(a.tree, '.seeded.tsv'), 'a')
for m in order:
    ol = os.path.join(a.tree, m + '.olean')
    sp = os.path.join(a.tree, '.stamps', m.replace('/', '__'))
    have = open(sp).read().strip() if os.path.exists(sp) else None
    if m not in a.target and have == cur[m] and os.path.exists(ol):
        continue
    if (m not in a.target and base.get(m) == cur[m] and m in booted
            and leadhead == '01cc6259480ccc9372181cd4d18d4511c87aa048'):
        os.makedirs(os.path.dirname(ol), exist_ok=True)
        if os.path.exists(ol):
            os.remove(ol)
        shutil.copyfile(os.path.join(LEAD_TREE, m + '.olean'), ol)
        open(sp, 'w').write(cur[m])
        seedlog.write(f'{m}\t{cur[m]}\tcopied-from-lead\n'); seedlog.flush()
        continue
    lf = open(os.path.join(LEAD, '.lean.lock'), 'w')
    fcntl.flock(lf, fcntl.LOCK_EX)
    t0 = time.time()
    lp = os.path.join(log, m.replace('/', '__') + '.log')
    with open(lp, 'wb') as out:
        rc = subprocess.run(['bash', os.path.join(a.wt, 'scripts/lean_check_tree.sh'), m],
                            cwd=a.wt, env=dict(os.environ, TCSLIB_OLEANS=a.tree),
                            stdout=out, stderr=subprocess.STDOUT).returncode
    fcntl.flock(lf, fcntl.LOCK_UN); lf.close()
    text = open(lp, encoding='utf-8', errors='replace').read()
    errs = len(ERR.findall(text))
    print(f'BUILT {m} rc={rc} errors={errs} sorry={text.count(chr(39)+"sorry"+chr(39))} '
          f'{time.time()-t0:.1f}s log={lp}', flush=True)
    if rc != 0 or errs:
        if os.path.exists(sp):
            os.remove(sp)
        print(text[-6000:])
        sys.exit(1)
    open(sp, 'w').write(cur[m])
    time.sleep(2)
print('OK', ' '.join(a.target))
