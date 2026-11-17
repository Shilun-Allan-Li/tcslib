#!/usr/bin/env python3
"""insertion_check.py <repo> <base-rev> <anchors.json> <outdir> [--head-dir DIR]   (cleanup-stage1, check 5)

For every changed existing file listed in anchors.json ({path: [{"after": <base line no>,
"text": <exact base line text>, "what": <label>}, ...]}):
  * read the base bytes (`git show <base-rev>:<path>`) and the head bytes (the file in --head-dir,
    default <repo>);
  * diff the line sequences (difflib, no junk heuristics), each inserted block slid down to its
    canonical position (while its first line equals the line after it); PASS requires that every opcode is
    `equal` or `insert` (no `replace`, no `delete`), that every inserted block starts right after a
    declared anchor (its base line number and exact text), and that removing the inserted blocks
    restores the base bytes exactly (byte comparison);
  * prints one record per block (base anchor line, inserted line count, first inserted line) and the
    final SHA-256 of base and head.
Controls (--controls): runs the same check on four mutated copies of each head file and requires
the stated result: (1) one character changed in a base line: FAIL with exactly one difference
(one `replace` of one line); (2) one base line deleted: FAIL with exactly one removal; (3) one extra
line inserted away from every anchor: FAIL (block not at an anchor); (4) an inserted block moved
to another place: FAIL.
Exit 0 iff every real file passes (and, with --controls, every control gives its stated result).
"""
import difflib, hashlib, json, os, re, subprocess, sys

args = sys.argv[1:]
controls = '--controls' in args
args = [a for a in args if a != '--controls']
headdir = None
if '--head-dir' in args:
    i = args.index('--head-dir'); headdir = args[i + 1]; del args[i:i + 2]
repo, base, anchf, outdir = args
headdir = headdir or repo
os.makedirs(outdir, exist_ok=True)
A = json.load(open(anchf))
sha = lambda b: hashlib.sha256(b).hexdigest()


def check(path, bbytes, hbytes, anchors):
    b = bbytes.decode('utf-8').split('\n')
    h = hbytes.decode('utf-8').split('\n')
    sm = difflib.SequenceMatcher(None, b, h, autojunk=False)
    ops = sm.get_opcodes()
    problems, blocks = [], []
    allowed = {a['after']: a for a in anchors}
    keep = []
    slid = 0
    for tag, i1, i2, j1, j2 in ops:
        if tag == 'equal':
            keep.extend(h[j1 + slid:j2]); slid = 0; continue
        if tag == 'insert':
            # canonical position: slide the block down while its first line equals the line after
            # it (diff alignment is ambiguous there; the bytes are the same)
            while j2 < len(h) and h[j1] == h[j2]:
                keep.append(h[j1]); i1 += 1; j1 += 1; j2 += 1; slid += 1
            a = allowed.get(i1)
            ok = a is not None and (i1 == 0 or b[i1 - 1] == a['text'])
            blocks.append(dict(after=i1, lines=j2 - j1, first=h[j1], at_anchor=ok,
                               what=a['what'] if a else None))
            if not ok:
                problems.append(f'insertion of {j2 - j1} line(s) after base line {i1} is not at an anchor')
            continue
        if tag == 'delete':
            problems.append(f'removal of base lines {i1 + 1}-{i2}')
        else:
            problems.append(f'replace of base lines {i1 + 1}-{i2} by head lines {j1 + 1}-{j2}')
            keep.extend(h[j1:j2])
    restored = '\n'.join(keep).encode('utf-8')
    if restored != bbytes and not any(p.startswith(('removal', 'replace')) for p in problems):
        problems.append('removing the inserted blocks does not restore the base bytes')
    return dict(path=path, ok=not problems, problems=problems, blocks=blocks,
                restores_base=restored == bbytes, base_sha256=sha(bbytes), head_sha256=sha(hbytes))


res, allok = [], True
for path, anchors in sorted(A.items()):
    bb = subprocess.run(['git', '-C', repo, 'show', f'{base}:{path}'], capture_output=True,
                        check=True).stdout
    hb = open(os.path.join(headdir, path), 'rb').read()
    r = check(path, bb, hb, anchors)
    allok &= r['ok']
    res.append(r)
    print(('PASS ' if r['ok'] else 'FAIL ') + path + f"  blocks={len(r['blocks'])} "
          f"restores_base={r['restores_base']} base={r['base_sha256'][:12]} head={r['head_sha256'][:12]}")
    for blk in r['blocks']:
        print(f"    after base line {blk['after']} ({blk['what']}): +{blk['lines']} | {blk['first'][:70]}")
    for p in r['problems']:
        print('    PROBLEM', p)
json.dump(res, open(os.path.join(outdir, 'insertion-check.json'), 'w'), indent=1)
print('RESULT', 'PASS' if allok else 'FAIL', f'{len(res)} files')

if controls:
    cres, call = [], True
    for path, anchors in sorted(A.items()):
        bb = subprocess.run(['git', '-C', repo, 'show', f'{base}:{path}'], capture_output=True,
                            check=True).stdout
        hb = open(os.path.join(headdir, path), 'rb').read()
        b = bb.decode().split('\n'); h = hb.decode().split('\n')
        sm = difflib.SequenceMatcher(None, b, h, autojunk=False)
        eq = [(i1, j1) for t, i1, i2, j1, j2 in sm.get_opcodes() if t == 'equal' and i2 - i1 > 3]
        ins = [(i1, j1, j2) for t, i1, i2, j1, j2 in sm.get_opcodes() if t == 'insert']
        # (1) change one character of a base line (a non-empty line in an equal run)
        _, j = eq[0]; j += 1
        while not h[j].strip():
            j += 1
        m1 = h[:]; m1[j] = m1[j][:-1] + ('X' if m1[j][-1] != 'X' else 'Y')
        r1 = check(path, bb, '\n'.join(m1).encode(), anchors)
        mm = re.match(r'replace of base lines (\d+)-(\d+) by head lines (\d+)-(\d+)$',
                      r1['problems'][0]) if len(r1['problems']) == 1 else None
        c1 = (not r1['ok']) and mm is not None and mm.group(1) == mm.group(2) \
            and mm.group(3) == mm.group(4)
        # (2) delete one base line
        m2 = h[:j] + h[j + 1:]
        r2 = check(path, bb, '\n'.join(m2).encode(), anchors)
        c2 = (not r2['ok']) and len(r2['problems']) == 1 and r2['problems'][0].startswith('removal')
        # (3) an extra line away from every anchor (two lines after the changed line's run start)
        m3 = h[:j + 1] + ['-- extra line'] + h[j + 1:]
        r3 = check(path, bb, '\n'.join(m3).encode(), anchors)
        c3 = not r3['ok']
        # (4) move the first inserted block to the start of the first long equal run
        i1, j1, j2 = ins[0]
        blk = h[j1:j2]; rest = h[:j1] + h[j2:]
        k = 2 if j1 > 10 else len(rest) - 3
        m4 = rest[:k] + blk + rest[k:]
        r4 = check(path, bb, '\n'.join(m4).encode(), anchors)
        c4 = not r4['ok']
        ok = c1 and c2 and c3 and c4
        call &= ok
        rec = dict(path=path, char_changed=dict(expected='FAIL, exactly one difference', ok=c1,
                                                problems=r1['problems']),
                   line_deleted=dict(expected='FAIL, exactly one removal', ok=c2, problems=r2['problems']),
                   extra_line=dict(expected='FAIL', ok=c3, problems=r3['problems']),
                   block_moved=dict(expected='FAIL', ok=c4, problems=r4['problems']))
        cres.append(rec)
        print(('CTL-OK  ' if ok else 'CTL-BAD ') + path, c1, c2, c3, c4)
    json.dump(cres, open(os.path.join(outdir, 'insertion-controls.json'), 'w'), indent=1)
    print('CONTROLS', 'ALL_OK' if call else 'NOT_OK')
    allok &= call
sys.exit(0 if allok else 1)
