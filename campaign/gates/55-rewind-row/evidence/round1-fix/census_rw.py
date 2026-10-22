"""Gate 55 review: recompute Build/Rewind.lean's copy-text census independently.

Uses copy-text-screen-v3's measure (comments stripped, whitespace removed, body after the first
depth-0 `:=` or `|`/`where`, greedy tiling with blocks >= 25, like-kind, member when the target
reproduces >= half of the source body and >= 60 characters), restricted to pairs with a Rewind
declaration on one side. Also prints each Rewind declaration's body length (screened or not),
the longest common contiguous segment for every reported pair, and a library-wide widening.
Usage: python3 -I census_rw.py <rewind.lean> <out-prefix> <file.lean> [<file.lean> ...]
Each further file is given as path[=label].
"""
import re, sys

rw_path, outp, others = sys.argv[1], sys.argv[2], sys.argv[3:]


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


def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''


def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best


def tiled(a, b):
    c = 0; tiles = []
    while True:
        n, seg = lcs(a, b)
        if n < 25: return c, tiles
        c += n; tiles.append(seg); a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)


grams = lambda x: {x[i:i + 25] for i in range(len(x) - 24)}


def decls(path, label, keep_short=False):
    t = strip(open(path, encoding='utf-8').read()); ms = list(DECL.finditer(t)); res = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        if len(bd) >= 60 or keep_short:
            res.append((label, m.group(3), kind, bd, m.group(1).strip() + ' ' + m.group(2)))
    return res


rw_all = decls(rw_path, 'Rewind.lean', keep_short=True)
rw = [d for d in rw_all if len(d[3]) >= 60]
lines = ['# Rewind declarations (all, with extracted body length; screened iff >= 60)']
for (_, nm, kind, bd, kw) in rw_all:
    lines.append(f'   {kw:>20} {nm}: kind={kind} body={len(bd)} screened={len(bd) >= 60}')
pairs = []
for spec in others:
    path, _, label = spec.partition('=')
    label = label or path.rsplit('/', 1)[-1]
    try:
        od = decls(path, label)
    except (UnicodeDecodeError, OSError) as e:
        lines.append(f'   skipped {path}: {e}'); continue
    for (la, a, ka, ta, _) in rw:
        ga = grams(ta)
        for (lb, b, kb, tb, _) in od:
            if lb == la and a == b: continue
            if not (ga & grams(tb)): continue
            for (src_l, src, src_t, tgt_l, tgt, tgt_t, ksrc, ktgt) in (
                    (lb, b, tb, la, a, ta, kb, ka), (la, a, ta, lb, b, tb, ka, kb)):
                sh, tiles = tiled(src_t, tgt_t)
                if sh >= 60 and 2 * sh >= len(src_t):
                    L, seg = lcs(src_t, tgt_t)
                    pairs.append((sh / len(src_t), f'{tgt_l}::{tgt}', f'{src_l}::{src}', sh,
                                  len(src_t), L, ksrc == ktgt, ksrc, ktgt, seg, tiles))
pairs.sort(key=lambda p: -p[0])
lines.append('')
lines.append('# Pairs with a Rewind declaration on one side (target reproduces >= half of source, '
             '>= 60 chars); like-kind flag shown, unlike-kind pairs are not members')
for (fr, tgt, src, sh, ln, L, like, ks, kt, seg, tiles) in pairs:
    lines.append(f'   {tgt}  reproduces  {src}: {sh}/{ln} = {fr:.0%}; longest contiguous {L}; '
                 f'like-kind={like} ({kt} vs {ks}); tiles={[len(x) for x in tiles]}')
    lines.append(f'      longest segment: {seg}')
    lines.append(f'      tiles: {tiles}')
open(outp, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
