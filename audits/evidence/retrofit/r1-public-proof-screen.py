"""Retrofit-R1 public-proof screen (round-5 repair).

Implements the method stated in audits/duplication-ledger.md: for each public
`computesFunInTime_X` of Composition/Primitives with a Catalog
`computesFunInTime_X_spaceUsed`, take the source proof after its top-level `:=`,
rename source identifiers `h` to `f2_h` where Catalog declares `f2_h`, strip
comments and ALL whitespace, and report the longest common contiguous segment
with the target's proof (Unicode characters). Candidate threshold: 60.
A second pass screens the 27 recorded F2A nonmembers against every public proof
of Composition, Primitives and ClassP/TimeConstructible.
Usage: python3 -I r1-public-proof-screen.py <repo-root>
"""
import re, sys
root = sys.argv[1]
F = {'Catalog': 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean',
     'Primitives': 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',
     'Composition': 'TCSlib/Complexity/TuringMachine/Composition.lean',
     'TimeConstructible': 'TCSlib/Complexity/ClassP/TimeConstructible.lean'}
NONMEMBERS = """f2_polyHeads f2_polyHeads_bounds f2_poly_step f2_head_steps f2_poly_space
f2_counter_count_space f2_counter_heads f2_counter_space f2_space_of_time f2_unary_sharp
f2_first_length f2_strip_linear f2_loopCall_heads f2_segment_heads f2_space_radius
f2_seamed_space f2_exists_loopFind_space f2_cond_time f2_rewind_scan_heads f2_rewind_heads
f2_branch_space f2_condHeads f2_control_heads f2_branch_heads f2_read_heads f2_cond_ledger
f2_cond_space""".split()
assert len(NONMEMBERS) == 27
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def decls(path):
    t = strip(open(f'{root}/{path}', encoding='utf-8').read())
    ms = list(DECL.finditer(t)); out = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        out[m.group(3)] = ('private' in m.group(1), t[m.start():end])
    return out
def proof(body):
    d = 0
    for i, ch in enumerate(body):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif body.startswith(':=', i) and d == 0: return body[i + 2:]
    return ''
D = {k: decls(v) for k, v in F.items()}
f2 = {n for n in D['Catalog'] if n.startswith('f2_')}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")  # dotted names split, so `idTM.ComputesInTime` renames its head
def rename(s):
    return IDENT.sub(lambda m: ('f2_' + m.group(0)) if ('f2_' + m.group(0)) in f2 else m.group(0), s)
squash = lambda s: re.sub(r'\s+', '', s)
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiled(a, b, minlen=25):
    """Greedy string tiling: repeatedly take the longest common block of the still
    unmarked text (>= minlen chars) and mask it on both sides; return the total
    shared length (a's characters reproduced in b)."""
    covered = 0
    while True:
        n, seg = lcs(a, b)
        if n < minlen: return covered
        covered += n
        a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
def verdict(shared, src_len):
    """Classification rule (round-5 repair): a pair is a MEMBER when at least half of
    the SOURCE proof reappears in the target (R4-1's standard: the source proof is
    reproduced inside the target), with an absolute floor of 60 shared characters so
    a short citation of a public lemma is reuse, not duplication. Otherwise any shared
    tiling >= 60 chars is a recorded FRAGMENT; anything else is no candidate."""
    if shared >= 60 and shared >= 0.5 * src_len: return 'MEMBER'
    if shared >= 60: return 'fragment (recorded)'
    return 'citation/none' if shared else 'none'
print("== Pass 1: direct public pairs (source computesFunInTime_X  ->  Catalog X_spaceUsed)")
pairs = 0
for src in ('Composition', 'Primitives'):
    for name, (priv, body) in D[src].items():
        if priv or not name.startswith('computesFunInTime_'): continue
        tgt = name + '_spaceUsed'
        if tgt not in D['Catalog']: print(f"   {src:11s} {name[18:]:16s} (no Catalog counterpart)"); continue
        pairs += 1
        a, b = squash(rename(proof(body))), squash(proof(D['Catalog'][tgt][1]))
        n, seg = lcs(a, b); sh = tiled(a, b)
        print(f"   {src:11s} {name[18:]:16s} LCS {n:4d} {'(>=60)' if n >= 60 else '      '}  shared {sh:4d} = {sh/len(a):5.1%} of source {len(a):5d}  -> {verdict(sh, len(a))}")
print(f"   eligible pairs: {pairs}")
print("== Pass 2: the 27 F2A nonmembers against every public proof of Composition/Primitives/TimeConstructible")
pubs = [(s, n, squash(rename(proof(b)))) for s in ('Composition', 'Primitives', 'TimeConstructible')
        for n, (p, b) in D[s].items() if not p]
for nm in NONMEMBERS:
    tb = squash(proof(D['Catalog'][nm][1]))
    best = max(((tiled(pb, tb), lcs(pb, tb)[0], s, n, pb) for s, n, pb in pubs), default=(0, 0, '', '', ''))
    sh, best = best[0], best[1:]
    print(f"   {nm:26s} LCS {best[0]:4d} {'(>=60)' if best[0] >= 60 else '      '}  shared {sh:4d} = {sh/len(best[3]):5.1%} of source {len(best[3]):5d}  vs {best[1]}::{best[2]}  -> {verdict(sh, len(best[3]))}")

# ---- physical spans (docstring-inclusive): from the attached docstring through the last code line
def span(path, name):
    L = open(f'{root}/{path}', encoding='utf-8').read().split('\n')
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s+" + re.escape(name) + r"(?:\s|$)")
    i = next(k for k, l in enumerate(L) if pat.match(l))
    start = i
    while start > 0 and L[start - 1].startswith('@['): start -= 1
    if start > 0 and L[start - 1].rstrip().endswith('-/'):
        j = start - 1
        while not L[j].lstrip().startswith('/--'): j -= 1
        start = j
    nxt = re.compile(r"^(?:/--|/-!|@\[|(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s|end\b|namespace\b|section\b|open\b|variable\b|set_option\b)")
    k = i + 1
    while k < len(L) and not nxt.match(L[k]): k += 1
    end = k - 1
    while L[end].strip() == '': end -= 1
    return end - start + 1
if len(sys.argv) > 2 and sys.argv[2] == '--spans':
    for f, n in [('Primitives','computesFunInTime_stripLast'),('Catalog','f2_strip_linear'),('Catalog','computesFunInTime_id_spaceUsed'),('Catalog','computesFunInTime_const_spaceUsed'),
                 ('Catalog','f2_counter_heads'),('Catalog','computesFunInTime_prepend_spaceUsed'),('Catalog','computesFunInTime_pairEncodeFixed_spaceUsed'),
                 ('Catalog','computesFunInTime_pairFst_spaceUsed'),('Catalog','computesFunInTime_pairSnd_spaceUsed'),('Catalog','computesFunInTime_pairConcat_spaceUsed'),
                 ('Primitives','computesFunInTime_prepend'),('Primitives','computesFunInTime_pairEncodeFixed'),('Primitives','computesFunInTime_pairFst'),
                 ('Primitives','computesFunInTime_pairSnd'),('Primitives','computesFunInTime_pairConcat')]:
        print(f"SPAN {f}::{n} = {span(F[f], n)}")
