# package.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW, the delivery packaging (brief, Checks item 8; Branches,
# trees and delivery). Usage: python3 -I package.py <delivery-dir> <plan.json> <out-filelist>
# The working data stays where it was produced (under <delivery-dir>/evidence, untracked unless delivered). The plan names
#   "plain": files or globs (relative to evidence/) delivered as they are;
#   "zip":   groups {"name", "globs", "only_done": [rundir...]} written into numbered parts evidence/zip/<name>.partNN.zip of at
#            most 90 MB (deflate 9), each with <name>.partNN.entries.txt (path, bytes, SHA-256 of the uncompressed file);
#            with only_done, a log under <rundir>/mods is packed only when its probe has a record in <rundir>/results*.jsonl
#            (logs of running probes are left for the next delivery).
# Then evidence/SHA256SUMS lists every delivered evidence file except itself and the top-level SHA256SUMS every delivered
# file except itself (sha256sum format, relative paths, no leading ./); <out-filelist> lists the delivered paths for
# `git add`. Previous parts of a group are replaced, unless (change, final) the group's files equal its entries lists exactly,
# in which case the parts are kept as they are. Nothing is moved or deleted outside evidence/zip/.
import sys, os, zipfile, hashlib, glob, json
dl, planp, outl = sys.argv[1:4]; ev = os.path.join(dl, 'evidence'); zd = os.path.join(ev, 'zip'); os.makedirs(zd, exist_ok=True)
plan = json.load(open(planp)); LIM = 87 * 1000 * 1000
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()
def expand(gs): return sorted({os.path.relpath(p, ev) for g in gs for p in glob.glob(os.path.join(ev, g), recursive=True) if os.path.isfile(p)})
delivered = set()
for p in expand(plan['plain']): delivered.add('evidence/' + p)
for grp in plan['zip']:
    files = expand(grp['globs'])
    for rd in grp.get('only_done', []):
        done = set()
        for f in glob.glob(os.path.join(ev, rd, 'results*.jsonl')):
            for l in open(f):
                x = json.loads(l)
                if 'module' in x: done.add(x['module'].replace('/', '_') + '.log')
        files = [p for p in files if not (p.startswith(rd + '/mods/') and os.path.basename(p) not in done)]
    # keep the existing parts when their entries list exactly these files with the same size and SHA-256 (no re-zip, so the
    # delivered bytes do not change)
    oldents = sorted(glob.glob(os.path.join(zd, grp['name'] + '.part*.entries.txt')))
    if oldents:
        have = sorted(tuple(l.rstrip('\n').split('\t')) for e in oldents for l in open(e) if l.strip())
        want = sorted((p, str(os.path.getsize(os.path.join(ev, p))), sha(os.path.join(ev, p))) for p in files)
        if have == want:
            for e in oldents:
                delivered.add(os.path.relpath(e, dl)); delivered.add(os.path.relpath(e.replace('.entries.txt', '.zip'), dl))
            print(grp['name'], 'unchanged, kept', len(oldents), 'parts'); continue
    for old in glob.glob(os.path.join(zd, grp['name'] + '.part*')): os.remove(old)
    part, z, ents, size = 0, None, [], 0
    def close():
        global z, ents
        if z is not None:
            z.close(); en = os.path.join(zd, f"{grp['name']}.part{part:02d}.entries.txt")
            open(en, 'w').write(''.join(f'{a}\t{b}\t{c}\n' for a, b, c in ents))
            delivered.add(os.path.relpath(en, dl)); delivered.add(os.path.relpath(zp, dl))
        z, ents = None, []
    for p in files:
        if z is None:
            part += 1; zp = os.path.join(zd, f"{grp['name']}.part{part:02d}.zip"); z = zipfile.ZipFile(zp, 'w', zipfile.ZIP_DEFLATED, compresslevel=9)
        a = os.path.join(ev, p); z.write(a, p); ents.append((p, os.path.getsize(a), sha(a)))
        z.fp.flush()
        if os.path.getsize(zp) > LIM: close()
    close()
    print(grp['name'], 'files', len(files), 'parts', part)
evf = sorted(p for p in delivered if p.startswith('evidence/') and p != 'evidence/SHA256SUMS')
open(os.path.join(ev, 'SHA256SUMS'), 'w').write(''.join(f"{sha(os.path.join(dl, p))}  {p[len('evidence/'):]}\n" for p in evf))
delivered.add('evidence/SHA256SUMS')
for p in plan.get('top', []): delivered.add(p)
top = sorted(p for p in delivered if p != 'SHA256SUMS')
open(os.path.join(dl, 'SHA256SUMS'), 'w').write(''.join(f'{sha(os.path.join(dl, p))}  {p}\n' for p in top))
open(outl, 'w').write(''.join(p + '\n' for p in top + ['SHA256SUMS']))
big = [p for p in top if os.path.getsize(os.path.join(dl, p)) > 95 * 1000 * 1000]
print('evidence files', len(evf), 'delivered', len(top) + 1, 'bytes', sum(os.path.getsize(os.path.join(dl, p)) for p in top), 'over 95 MB', big)
