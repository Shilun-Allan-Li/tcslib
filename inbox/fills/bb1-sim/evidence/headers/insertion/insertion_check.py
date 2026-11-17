# ADAPTED (bb1-sim, lead, 2026-11-17) from T4's evidence/headers/insertion/insertion_check.py
# (exchange inbox/fills/bb1-machine, f14ac810). Changes: SRC_SHA and SPEC for the ten approved
# readers of bb1-sim (the pack's readers/Defs-block.lean.txt, lines 1-86 of the combined source,
# and readers/BonehBoyen-block.lean.txt, lines 87-131; the combined source is the two blocks
# concatenated); anchors are located by their base line number (the Defs anchor line
# `  (OracleComp.bind_pure _).symm` is not unique) and, in the head, by the anchor line followed
# verbatim by the block; the docstring below is T4's, read with these changes.
"""insertion_check.py <base-Defs> <head-Defs> <base-BonehBoyen> <head-BonehBoyen> <readers.txt>

Reader-insertion check of fill bb1-machine (brief: "Target and approved readers", "Checks and
report" -> "Headers and insertions"). Run as `python3 -I insertion_check.py ...`.

Inputs: the issue-base (7c0a55e0) and head versions of
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/{Defs,BonehBoyen}.lean and the approved
source scope-request/BB1ReadersMin.lean.txt. Three blocks are expected, each = one blank line
followed by approved source lines, inserted right after an anchor line:
  D1 Defs.lean       after `    S.oracleImpl κ init key chal 2 x s = chal x s := rfl`  (base 387)
                     approved lines 27-68 (oracleImpl_{zero,one,two}_onSpec)
  B1 BonehBoyen.lean after `  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme` (387)
                     approved lines 74-97 (ofFn_bb1Scheme_encPP/_encSK, bb1Scheme_msgSpace_iff)
  B2 BonehBoyen.lean after the last line of bb1SimCt_eq (base 551), approved lines 99-109
                     (ofFn_bb1SimCt)
Checks (each printed PASS/FAIL):
  C0 inputs: source/base SHA-256s and line counts; anchors unique in the base, at the stated lines
  C1 each block is located verbatim right after its (unique) anchor in the head file
  C2 each of the seven readers (by theorem name) is declared exactly once over both head files,
     its text equals the approved text byte for byte, at its position in its block (the position
     counts the preceding readers of the block that are present, so a deleted reader is
     reported once, as MISSING, and its successors are not reported as MOVED)
  C3 removing the blocks (with their leading blank lines) restores the base byte for byte
  C4 final SHA-256s and line counts of the head files
  C5 difflib line diff head vs base: exactly the inserted lines (ADDED 43 / 37, 0 REMOVED,
     0 CHANGED)
  C6 difflib line diff head vs expected head (base + verbatim blocks): 0 differing lines
Machine-readable summary lines: `READERS ok=.. missing=[..] duplicate=[..] moved=[..]
textdiff=[..]` and `DIFF_VS_EXPECTED <file> added=.. removed=.. changed=..`.
Final line `RESULT PASS` (exit 0) or `RESULT FAIL` (exit 1).

written by tools-agent (sub-agent), fill bb1-machine
"""
import difflib
import hashlib
import re
import sys

SRC_SHA = '7836f034f717062fe8713434e9f1a97d3bfee125621ea3a94a54c0d44343773a'
SPEC = {
    'Defs': dict(
        base_sha='4e220eadd4bf71ea62372bc371a3e2062b9f213acc696dbb66994c1f64069dfd',
        head_sha='97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0',
        base_n=476, head_n=563, added=87,
        blocks=[('D1', '  (OracleComp.bind_pure _).symm', 430, 1, 86)]),
    'BonehBoyen': dict(
        base_sha='da875140806706f26c4cdbb5cf765f522144f3a5a885c5156a58b8c611cd25f4',
        head_sha='88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26',
        base_n=714, head_n=760, added=46,
        blocks=[('B1', '  exists_congr fun _ => List.ofFn_inj.symm', 412, 87, 131)]),
}
DECL = r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+'

results = []


def check(tag, ok, msg):
    results.append(ok)
    print(f'[{"PASS" if ok else "FAIL"}] {tag}: {msg}')


def sha(s):
    return hashlib.sha256(s.encode('utf-8')).hexdigest()


def nlines(s):
    return s.count('\n')


def read(p):
    with open(p, 'rb') as fh:
        return fh.read().decode('utf-8')


def readers_of(block):
    """Split an approved block (list of lines) at blank lines; return [(name, start, lines)]."""
    out, cur, start = [], [], 0
    for i, ln in enumerate(block + ['']):
        if ln == '':
            if cur:
                names = [m.group(1) for x in cur for m in [re.match(DECL + r'(\S+)', x)] if m]
                assert len(names) == 1 and cur[0].startswith('/--'), cur[:2]
                out.append((names[0], start, cur))
            cur, start = [], i + 1
        else:
            cur.append(ln)
    return out


def diff_counts(a, b):
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    add = rem = chg = 0
    hunks = []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            continue
        if op == 'insert':
            add += j2 - j1
        elif op == 'delete':
            rem += i2 - i1
        else:
            chg += max(i2 - i1, j2 - j1)
        hunks.append((op, i1, i2, j1, j2))
    return add, rem, chg, hunks


def show_hunks(a, b, hunks, limit=8):
    for op, i1, i2, j1, j2 in hunks[:limit]:
        print(f'      {op} base/exp {i1 + 1}-{i2} head {j1 + 1}-{j2}')
        for k in range(i1, min(i2, i1 + 3)):
            print(f'        - {k + 1}: {a[k]!r}'[:200])
        for k in range(j1, min(j2, j1 + 3)):
            print(f'        + {k + 1}: {b[k]!r}'[:200])
    if len(hunks) > limit:
        print(f'      ... {len(hunks) - limit} more hunk(s)')


def main(argv):
    if len(argv) != 6:
        print(__doc__)
        return 2
    bD, hD, bB, hB, srcp = argv[1:6]
    src = read(srcp)
    A = src.split('\n')
    check('C0 source', sha(src) == SRC_SHA, f'{srcp} sha256 {sha(src)}')
    files = {'Defs': (read(bD), read(hD)), 'BonehBoyen': (read(bB), read(hB))}
    # expected readers: name -> (file, block tag, offset in block, lines)
    want = {}
    exp_heads = {}
    for f, sp in SPEC.items():
        base, head = files[f]
        check(f'C0 base {f}', sha(base) == sp['base_sha'] and nlines(base) == sp['base_n'],
              f'{nlines(base)} lines sha256 {sha(base)}')
        BL = base.split('\n')
        E = list(BL)
        for tag, anc, at, a, b in sorted(sp['blocks'], key=lambda t: -t[2]):
            idx = [at - 1] if at - 1 < len(BL) and BL[at - 1] == anc else []
            check(f'C0 base anchor {tag}', idx == [at - 1], f'anchor {anc!r} at base line {at}: '
                  f'{bool(idx)}')
            if idx:
                E[idx[0] + 1:idx[0] + 1] = [''] + A[a - 1:b]
            for name, off, lines in readers_of(A[a - 1:b]):
                want[name] = (f, tag, off, lines)
        exp_heads[f] = E
    print(f'      approved readers: {len(want)} {sorted(want)}')
    # C1 locate blocks
    located = {}
    for f, sp in SPEC.items():
        HL = files[f][1].split('\n')
        for tag, anc, at, a, b in sp['blocks']:
            blk = [''] + A[a - 1:b]
            idx = [i for i, x in enumerate(HL) if x == anc
                   and HL[i + 1:i + 1 + len(blk)] == blk]
            if len(idx) != 1:
                idx = [at - 1] if at - 1 < len(HL) and HL[at - 1] == anc else []
            if len(idx) != 1:
                check(f'C1 block {tag} ({f})', False, f'anchor not found at head line {at} and '
                      f'not followed verbatim by the block anywhere')
                continue
            s = idx[0] + 1
            win = HL[s:s + len(blk)]
            bad = [k for k in range(len(blk)) if k >= len(win) or win[k] != blk[k]]
            if not bad:
                located[tag] = (s, len(blk))
                check(f'C1 block {tag} ({f})', True, f'verbatim at head lines {s + 1}-'
                      f'{s + len(blk)} (blank + approved {a}-{b}), after anchor line {s}')
            else:
                check(f'C1 block {tag} ({f})', False, f'{len(bad)} of {len(blk)} lines differ '
                      f'positionally in the window after anchor line {s}')
                for k in bad[:4]:
                    print(f'        line {s + k + 1}: want {blk[k]!r}'[:200])
                    print(f'        line {s + k + 1}: have {win[k] if k < len(win) else None!r}'
                          [:200])
    # C2 readers
    heads = {f: files[f][1].split('\n') for f in files}
    anchors = {}
    for f, sp in SPEC.items():
        for tag, anc, at, *_ in sp['blocks']:
            anchors[tag] = located[tag][0] - 1 if tag in located else (
                at - 1 if at - 1 < len(heads[f]) and heads[f][at - 1] == anc else None)
    cat = {'ok': [], 'missing': [], 'duplicate': [], 'moved': [], 'textdiff': []}
    occs = {}
    for name in want:
        pat = re.compile(DECL + re.escape(name) + r'(?:\s|$)')
        occs[name] = [(g, i) for g in heads for i, x in enumerate(heads[g]) if pat.match(x)]
    for name in sorted(want, key=lambda n: (want[n][0], want[n][1], want[n][2])):
        f, tag, off, lines = want[name]
        pat = re.compile(DECL + re.escape(name) + r'(?:\s|$)')
        occ = occs[name]
        # expected start: right after the anchor's blank line, plus the approved length (and
        # separating blank line) of each preceding reader of the block that is present at all
        # (a deleted reader is reported once as MISSING and does not shift its successors)
        pre = [x for x in want if want[x][1] == tag and want[x][2] < off and occs[x]]
        shift = sum(len(want[x][3]) + 1 for x in pre)
        if not occ:
            cat['missing'].append(name)
            check(f'C2 reader {name}', False, 'MISSING (0 declarations in the head files)')
            continue
        if len(occ) > 1:
            cat['duplicate'].append(name)
            check(f'C2 reader {name}', False, f'DUPLICATE ({len(occ)} declarations: '
                  f'{[(g, i + 1) for g, i in occ]})')
            continue
        g, ti = occ[0]
        toff = next(k for k, x in enumerate(lines) if pat.match(x))
        st = ti - toff
        have = heads[g][st:st + len(lines)]
        nd = [k for k in range(len(lines)) if k >= len(have) or have[k] != lines[k]]
        # docstring start must also match (no extra/missing docstring lines)
        if st > 0 and heads[g][st - 1] != '':
            nd = nd or [-1]
        a0 = anchors.get(tag)
        exp_st = None if a0 is None else a0 + 2 + shift
        if nd:
            cat['textdiff'].append(name)
            check(f'C2 reader {name}', False, f'TEXT DIFFERS ({len([k for k in nd if k >= 0])} '
                  f'line(s)) in {g}.lean at lines {st + 1}-{st + len(lines)}')
            for k in nd[:4]:
                if k >= 0:
                    print(f'        line {st + k + 1}: want {lines[k]!r}'[:200])
                    print(f'        line {st + k + 1}: have {have[k] if k < len(have) else None!r}'
                          [:200])
                else:
                    print(f'        line {st}: expected a blank line before the docstring')
        elif g != f or st != exp_st:
            cat['moved'].append(name)
            check(f'C2 reader {name}', False, f'MOVED: verbatim in {g}.lean at line {st + 1}, '
                  f'expected {f}.lean line {None if exp_st is None else exp_st + 1} (block {tag})')
        else:
            cat['ok'].append(name)
            check(f'C2 reader {name}', True, f'once, verbatim, {g}.lean lines {st + 1}-'
                  f'{st + len(lines)} (block {tag}, offset {off})')
    print(f'READERS ok={len(cat["ok"])} missing={cat["missing"]} duplicate={cat["duplicate"]} '
          f'moved={cat["moved"]} textdiff={cat["textdiff"]}')
    # C3 removal, C4 hashes, C5 diff vs base, C6 diff vs expected
    for f, sp in SPEC.items():
        base, head = files[f]
        tags = [t[0] for t in sp['blocks']]
        if all(t in located for t in tags):
            HL = head.split('\n')
            for t in sorted(tags, key=lambda t: -located[t][0]):
                s, n = located[t]
                del HL[s:s + n]
            r = '\n'.join(HL)
            if r == base:
                check(f'C3 removal {f}', True, f'blocks {tags} removed: equals base byte for byte '
                      f'(sha256 {sha(r)})')
            else:
                a, b = base.split('\n'), r.split('\n')
                k = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]),
                         min(len(a), len(b)))
                check(f'C3 removal {f}', False, f'after removing {tags}: {len(b) - 1} lines vs '
                      f'base {len(a) - 1}; first difference at line {k + 1}: base '
                      f'{a[k] if k < len(a) else None!r} head {b[k] if k < len(b) else None!r}'
                      [:300])
        else:
            check(f'C3 removal {f}', False, f'blocks {[t for t in tags if t not in located]} not '
                  f'located verbatim; removal not applicable')
        check(f'C4 hash {f}', sha(head) == sp['head_sha'] and nlines(head) == sp['head_n'],
              f'{nlines(head)} lines sha256 {sha(head)} (expected {sp["head_n"]} '
              f'{sp["head_sha"]})')
        BL, HL = base.split('\n'), head.split('\n')
        add, rem, chg, hunks = diff_counts(BL, HL)
        # each inserted hunk must be one block: blank + approved lines, or (difflib may align
        # the block's leading blank line with the base's next blank line) approved lines + blank
        blks = [A[a - 1:b] for _, _, _, a, b in sp['blocks']]
        ins = [HL[j1:j2] for op, i1, i2, j1, j2 in hunks if op == 'insert']
        same = (len(ins) == len(blks)
                and all(x in ([''] + y, y + ['']) for x, y in zip(ins, blks)))
        ok = (add, rem, chg) == (sp['added'], 0, 0) and same
        check(f'C5 diff-vs-base {f}', ok, f'ADDED {add} REMOVED {rem} CHANGED {chg} in '
              f'{len(hunks)} hunk(s) (expected ADDED {sp["added"]} REMOVED 0 CHANGED 0); '
              f'inserted hunks {"are" if same else "are NOT"} exactly the approved blocks')
        for op, i1, i2, j1, j2 in hunks:
            print(f'      {op} after base line {i1}: head lines {j1 + 1}-{j2}'
                  + (f' / base lines {i1 + 1}-{i2}' if i2 > i1 else ''))
        EL = exp_heads[f]
        add, rem, chg, hunks = diff_counts(EL, HL)
        print(f'DIFF_VS_EXPECTED {f} added={add} removed={rem} changed={chg}')
        check(f'C6 diff-vs-expected {f}', add == rem == chg == 0,
              f'head vs base+verbatim blocks: ADDED {add} REMOVED {rem} CHANGED {chg}')
        show_hunks(EL, HL, hunks)
    ok = all(results)
    print(f'CHECKS {sum(results)}/{len(results)} PASS')
    print('RESULT', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
