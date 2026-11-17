r"""frozen_check.py <base-Relational> <head-Relational> <base-Security> <head-Security> (bb1-sim, Claude lead,
2026-11-17): the brief's frozen-header check (Checks, item 3). Run as `python3 -I`.
For each target (`expect_simulate_rel`, `expect_sample_rel` in Games/Relational.lean; `bb1_sim_real`,
`bb1_sim_random` in IdentityBased/BonehBoyenSecurity.lean):
  H1 the header (from `theorem <name>` through the line ending in `:= by`) is byte-identical to the base;
  H2 the statement prose (the docstring up to `**Proof sketch.**`) is byte-identical to the base.
  H3 `prob_simulate_rel` (Relational) and `bb1_sidSecure` (Security) are byte-identical whole (docstring, header,
     proof).
  H4 the rest of both files is unchanged: each file is normalized by replacing every target's sketch (from
     `**Proof sketch.**` to the end of its docstring) and body (the lines after its header up to the next line
     at column 0) by placeholders, dropping, in Security, the import lines of helper modules
     (`import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.<X>`) that directly follow
     the base's imports, and the `## Contents` section of the module docstring (from `## Contents` to the next
     `## ` heading); the normalized head must equal the normalized base byte for byte.
Prints PASS/FAIL per item and `RESULT PASS|FAIL` (exit 0/1)."""
import sys, re, hashlib
TGT = {'Relational': ['expect_simulate_rel', 'expect_sample_rel'], 'Security': ['bb1_sim_real', 'bb1_sim_random']}
WHOLE = {'Relational': ['prob_simulate_rel'], 'Security': ['bb1_sidSecure']}
HELPER = 'import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.'
res = []
def chk(tag, ok, msg=''):
    res.append(ok); print(f'[{"PASS" if ok else "FAIL"}] {tag}{": " + msg if msg else ""}')
def decl(L, name):
    """(doc_start, header_start, header_end, body_end) as 0-based line indices; body_end exclusive."""
    hs = [i for i, l in enumerate(L) if re.match(rf'^theorem {re.escape(name)}(\s|$)', l)]
    assert len(hs) == 1, (name, hs)
    h = hs[0]; d = h - 1
    while not L[d].startswith('/--'): d -= 1
    e = h
    while not L[e].rstrip().endswith(':= by') and not L[e].rstrip().endswith(':='): e += 1
    b = e + 1
    while b < len(L) and (L[b] == '' or L[b].startswith(' ')): b += 1
    while L[b - 1] == '': b -= 1
    return d, h, e + 1, b
def sketch_at(L, d, h):
    k = [i for i in range(d, h) if '**Proof sketch.**' in L[i]]
    return k[0] if k else None
def prose(L, d, h):
    k = sketch_at(L, d, h)
    if k is None: return '\n'.join(L[d:h])
    return '\n'.join(L[d:k]) + '\n' + L[k][:L[k].index('**Proof sketch.**')]
def normalize(L, kind):
    L = list(L)
    for name in TGT[kind]:
        d, h, e, b = decl(L, name)
        k = sketch_at(L, d, h)
        body = ['<BODY>']
        if k is not None:
            head = L[k][:L[k].index('**Proof sketch.**')] + '<SKETCH>'
            L = L[:k] + [head] + L[h:e] + body + L[b:]
        else:
            L = L[:e] + body + L[b:]
    if kind == 'Security':
        last = max(i for i, l in enumerate(L) if l.startswith('import ') and not l.startswith(HELPER))
        j = last + 1
        while j < len(L) and L[j].startswith(HELPER): j += 1
        L = L[:last + 1] + L[j:]
        if '## Contents' in L:
            a = L.index('## Contents'); z = a + 1
            while not L[z].startswith('## '): z += 1
            L = L[:a] + L[z:]
    return L
def main(a):
    files = {'Relational': (open(a[1], encoding='utf-8').read(), open(a[2], encoding='utf-8').read()),
             'Security': (open(a[3], encoding='utf-8').read(), open(a[4], encoding='utf-8').read())}
    for kind, (bs, hs) in files.items():
        BL, HL = bs.split('\n'), hs.split('\n')
        for name in TGT[kind]:
            try:
                bd, bh, be, _ = decl(BL, name); hd, hh, he, _ = decl(HL, name)
            except AssertionError as x:
                chk(f'H1 {name}', False, f'declaration not found once: {x}'); continue
            chk(f'H1 header {name}', BL[bh:be] == HL[hh:he], f'{be - bh} base lines, {he - hh} head lines')
            chk(f'H2 prose {name}', prose(BL, bd, bh) == prose(HL, hd, hh))
        for name in WHOLE[kind]:
            try:
                bd, bh, be, bb = decl(BL, name); hd, hh, he, hb = decl(HL, name)
                ok = BL[bd:bb] == HL[hd:hb]
            except AssertionError as x:
                ok = False
            chk(f'H3 whole {name}', ok)
        try:
            nb, nh = normalize(BL, kind), normalize(HL, kind)
            ok = nb == nh
            msg = f'normalized sha256 base {hashlib.sha256("\n".join(nb).encode()).hexdigest()[:16]} head {hashlib.sha256("\n".join(nh).encode()).hexdigest()[:16]}'
            if not ok:
                k = next((i for i in range(min(len(nb), len(nh))) if nb[i] != nh[i]), min(len(nb), len(nh)))
                msg += f'; first difference at normalized line {k + 1}: base {nb[k] if k < len(nb) else None!r} head {nh[k] if k < len(nh) else None!r}'[:300]
        except AssertionError as x:
            ok, msg = False, f'normalization failed: {x}'
        chk(f'H4 rest of {kind}', ok, msg)
    ok = all(res); print(f'CHECKS {sum(res)}/{len(res)} PASS'); print('RESULT', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1
if __name__ == '__main__': sys.exit(main(sys.argv))
