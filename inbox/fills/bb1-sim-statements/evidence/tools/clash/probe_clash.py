r"""probe_clash.py <repo> <out-dir> (bb1-sim-statements, lead): name-clash scan of the probe's reader
set (probe/READERS-TO-INSERT.md §2) with clash_scan.py's core (loaded by path from this directory).
For each owner, the head text is the owner at T4's head c90273fa with the block inserted after its
anchor (the sub-agent's insertion/ blocks; anchors Defs.lean:430, BonehBoyen.lean:412); the block's
declarations are classified against the base index (TCSlib/ and audits/) at the issue base
bdcadd85 and at T4's head c90273fa. Exit 0 iff no CLASH and no DUP-NEW at either base."""
import sys, os, importlib.util, subprocess
repo, out = sys.argv[1:3]
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('clash_scan', os.path.join(here, 'clash_scan.py'))
cs = importlib.util.module_from_spec(spec); spec.loader.exec_module(cs)
E = '/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/subagents/probe/insertion'
IB = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased'
T4 = 'c90273fad3511ada7c9c1a53e1abdd8478237cee'
owners = [(f'{IB}/Defs.lean', 430, f'{E}/Defs-block.lean.txt'),
          (f'{IB}/BonehBoyen.lean', 412, f'{E}/BonehBoyen-block.lean.txt')]
news = []
for path, anchor, blk in owners:
    base = subprocess.run(['git', '-C', repo, 'show', f'{T4}:{path}'], capture_output=True,
                          check=True).stdout.decode()
    ls = base.split('\n'); b = open(blk, encoding='utf-8').read()[:-1].split('\n')
    # the block files start with their own blank separator line or not: insert one blank line
    ins = ([''] if b[0] != '' else []) + b
    head = ls[:anchor] + ins + ls[anchor:]
    added = set(range(anchor + 1, anchor + len(ins) + 1))
    news += cs.added_decls('\n'.join(head), added, path)
os.makedirs(out, exist_ok=True)
bad = 0
for rev in ['bdcadd858cbe043e8c41e465a96e81feb1eecda1', T4]:
    idx = cs.base_index(repo, rev)
    rows = cs.classify(news, idx)
    k = sum(r['status'] in ('CLASH', 'DUP-NEW') for r in rows)
    bad += k
    with open(os.path.join(out, f'probe-readers-vs-{rev[:8]}.tsv'), 'w') as f:
        f.write(f'# index at {rev}: {idx["nfiles"]} files, {idx["ndecls"]} declarations\n')
        for r in rows:
            f.write('\t'.join([r['status'], r['full'], f'{r["path"]}:{r["line"]}',
                               cs.fmt_locs(r['clash']), cs.fmt_locs(r['info'])]) + '\n')
    print(rev[:8], len(rows), 'readers;', ', '.join(f'{s} {sum(r["status"] == s for r in rows)}'
          for s in ('OK', 'CLASH', 'DUP-NEW', 'MODIFIED')))
    for r in rows:
        print('  ', r['status'], r['full'], '| same short name:', cs.fmt_locs(r['info'], 4) or '-')
print('RESULT', 'PASS' if bad == 0 else 'FAIL')
sys.exit(0 if bad == 0 else 1)
