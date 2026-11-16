r"""frozen_check.py <base-file> <head-file> (fill-pair-bdh): frozen-header check of Pairing/Assumptions.lean.
Reverts exactly the permitted edits in the head file and requires the result to equal the base file byte for byte:
  (1) the four added import lines (each must be an `import` line placed right after the base's last import);
  (2) the two inserted helper blocks: [`/-! ### The Decision BDH distinguisher` .. `namespace BilinearGen`) and
      [`/-- **The reduction's bound**` .. `/-- **Decision BDH implies BDH**`); every declaration keyword line in them
      must be `private` (no public declaration may be added);
  (3) in T1 (`bdhAssumption_of_dbdhAssumption`): the `**Proof sketch.**` paragraph (to the docstring's end) and the
      body after the header line `    (h : G.DBDHAssumption) : G.BDHAssumption := by` (to `end BilinearGen`) are
      replaced by the base's. Everything else (all other declarations, T1's header, statement prose and Source
      paragraph, the module docstring) must be byte-identical. Prints PASS or FAIL with the first differing line."""
import sys, re
base = open(sys.argv[1], encoding='utf-8').read(); head = open(sys.argv[2], encoding='utf-8').read()
def fail(msg): print('FAIL:', msg); sys.exit(1)
# (1) imports
bi = re.findall(r'^import \S+\n', base, re.M); hi = re.findall(r'^import \S+\n', head, re.M)
if hi[:len(bi)] != bi: fail('base imports changed or reordered')
added = hi[len(bi):]
if len(added) != 4: fail(f'expected 4 added imports, found {len(added)}')
blk = ''.join(bi); i = head.index(blk) + len(blk)
if head[i:i + len(''.join(added))] != ''.join(added): fail('added imports not right after the base imports')
h = head[:i] + head[i + len(''.join(added)):]
# (2) helper blocks
def cut(s, a, b):
    if s.count(a) != 1 or s.count(b) != 1: fail(f'marker count: {a!r} {s.count(a)}, {b!r} {s.count(b)}')
    x = s.index(a); y = s.index(b)
    if not x < y: fail('marker order')
    seg = s[x:y]
    kw = re.findall(r'^((?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*)(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+(\S+)', seg, re.M)
    for pre, k, n in kw:
        if 'private' not in pre: fail(f'public declaration in inserted block: {k} {n}')
    return s[:x] + s[y:], [(k, n) for _, k, n in kw]
h, d1 = cut(h, '/-! ### The Decision BDH distinguisher', 'namespace BilinearGen\n')
h, d2 = cut(h, "/-- **The reduction's bound**", '/-- **Decision BDH implies BDH**')
# (3) T1 sketch and body
def seg(s, a, b):
    x = s.index(a); y = s.index(b, x); return x, y
HDR = '    (h : G.DBDHAssumption) : G.BDHAssumption := by\n'
for s, nm in ((base, 'base'), (h, 'head')):
    if s.count(HDR) != 1: fail(f'T1 header line count in {nm}: {s.count(HDR)}')
t1 = '/-- **Decision BDH implies BDH**'
bx, by = seg(base, '**Proof sketch.**', '-/\ntheorem bdhAssumption_of_dbdhAssumption\n')
if base.index(t1) > bx: fail('base sketch not in T1')
hx, hy = seg(h, '**Proof sketch.**', '-/\ntheorem bdhAssumption_of_dbdhAssumption\n')
if h.index(t1) > hx: fail('head sketch not in T1')
h = h[:hx] + base[bx:by] + h[hy:]
bb = base.index(HDR) + len(HDR); be = base.index('\nend BilinearGen', bb)
hb = h.index(HDR) + len(HDR); he = h.index('\nend BilinearGen', hb)
body_base, body_head = base[bb:be], h[hb:he]
h = h[:hb] + body_base + h[he:]
if h == base:
    print(f'PASS: reverted head == base ({len(base)} chars). added imports {len(added)}; inserted private declarations '
          f'{len(d1) + len(d2)}: ' + ', '.join(n for _, n in d1 + d2))
    print(f'T1 body base {body_base!r}; head body {len(body_head.splitlines())} lines; sorry in head body: {"sorry" in body_head}')
else:
    bl, hl = base.splitlines(), h.splitlines()
    k = next((j for j in range(min(len(bl), len(hl))) if bl[j] != hl[j]), min(len(bl), len(hl)))
    fail(f'reverted head differs from base at line {k + 1}: base {bl[k] if k < len(bl) else None!r} / '
         f'head {hl[k] if k < len(hl) else None!r}')
