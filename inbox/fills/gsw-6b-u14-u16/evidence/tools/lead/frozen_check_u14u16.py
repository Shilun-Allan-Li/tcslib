#!/usr/bin/env python3
"""frozen_check_u14u16.py <repo> <base> <head> <Bootstrap|Leveled> [--control N]  (gsw-6b-u14-u16,
C4; adapted from this host's frozen_check_u13.py, gsw-6b-u13, whose declaration cutter it keeps).

Checks that in the owned file everything but the regions COMMON §4 and the brief permit is
byte-identical to the base:
- every declaration is cut out of the base and head texts (from its doc comment or attribute line
  at column 0, or its declaration line, to the next such start or top-level command);
- for each target of the file: the doc comment up to `**Proof sketch.**` (the statement prose)
  and the header (keyword through the top-level `:= by`) must be byte-identical; the sketch
  paragraph and the proof body may change;
- every other base declaration (definitions, readers, G11, L1, the case readers) must be
  byte-identical;
- a head declaration not at the base is allowed only if it is `private` (a helper) or, in
  Bootstrap.lean only, the public helper `encrypts_bootGate`, which must sit immediately after G9
  (`encrypts_bootNAND`) and immediately before G10 (`decrypt_fheEval`);
- the non-declaration text (imports, options, namespace, `open`, the module docstring) must be
  identical, except the module-docstring line(s) saying that the targets are admitted and, in
  Bootstrap.lean only, the inserted `## Main results` entry for `encrypts_bootGate` (an insertion
  directly after the G9 entry whose lines mention `encrypts_bootGate`), and blank separator lines
  between declarations, at most one per added declaration.
Controls (--control N) alter the head text in memory and must each report exactly one violation:
1 a one-character header change; 2 an edit spilling from a sketch into the statement prose; 3 an
edit to a definition's body; 4 an edit to a reader; 5 an unpermitted import; 6 a deleted target;
7 an unlisted new public declaration; Bootstrap only: 8 `encrypts_bootGate` moved after G10
(ORDER); 9 an edit to another `## Main results` entry (TEXT). --control 0 compares the base with
itself."""
import sys, re, subprocess, difflib
repo, base, head, which = sys.argv[1:5]
ctl = int(sys.argv[sys.argv.index('--control') + 1]) if '--control' in sys.argv else None
D = 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/'
F = D + which + '.lean'
TARGETS = {'Bootstrap': ['encrypts_bootNAND', 'decrypt_fheEval', 'decrypt_fheEvalCircuit',
                         'decrypt_keygen_fheEvalCircuit', 'bootNoise_le'],
           'Leveled': ['encrypts_leveledEval', 'decrypt_keygen_leveledEvalCircuit']}[which]
HELPER = 'encrypts_bootGate' if which == 'Bootstrap' else None
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\s+([^\s(:{\[]+)')
TOP = re.compile(r'^(namespace|end|section|open|variable|universe|set_option|attribute|mutual|#|example|import|/-!)')
def git(*a): return subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True, check=True).stdout
def cut(text):
    L = text.split('\n'); starts = []
    k = 0
    while k < len(L):
        if L[k].startswith('/--'):
            j = k
            while '-/' not in L[j]: j += 1
            m = j + 1
            while m < len(L) and L[m].startswith('@['): m += 1
            if m < len(L) and DECL.match(L[m]): starts.append((k, DECL.match(L[m]).group(2))); k = m + 1; continue
            k = j + 1; continue
        if L[k].startswith('@[') or DECL.match(L[k]):
            m = k
            while m < len(L) and L[m].startswith('@['): m += 1
            if m < len(L) and DECL.match(L[m]): starts.append((k, DECL.match(L[m]).group(2))); k = m + 1; continue
        k += 1
    out = {}; spans = []
    for idx, (s, name) in enumerate(starts):
        e = starts[idx + 1][0] if idx + 1 < len(starts) else len(L)
        j = s + 1
        while j < e:
            if TOP.match(L[j]) or (L[j].startswith('/--') and j > s and not L[s].startswith('/--')): break
            j += 1
        while j > s and L[j - 1].strip() == '': j -= 1
        out[name] = '\n'.join(L[s:j]); spans.append((s, j))
    rest = [l for n, l in enumerate(L) if not any(a <= n < b for a, b in spans)]
    return out, rest
def split_target(t):
    """(prose, sketch, header, body) of a target's text."""
    d = t.index('-/') + 2
    doc, code = t[:d], t[d:]
    p = doc.index('**Proof sketch.**')
    m = re.search(r':= by\n', code)
    return doc[:p], doc[p:], code[:m.end()], code[m.end():]
def is_private(t):
    return any(re.match(r'^(?:@\[[^\]]*\]\s*)?(?:\w+\s+)*private\s', l) for l in t.split('\n')
               if DECL.match(l))
old, new = git('show', f'{base}:{F}'), git('show', f'{head}:{F}')
orig = new
R = lambda s, x, y: (s.replace(x, y, 1) if x in s else (_ for _ in ()).throw(SystemExit(f'control anchor missing: {x[:60]}')))
if ctl == 0: new = old
elif which == 'Bootstrap':
    if ctl == 1: new = R(new, 'theorem bootNoise_le (P', 'theorem bootNoise_le  (P')
    elif ctl == 2:
        new = R(new, 'with noise at most `bootNoise P βk`:\n`Encrypts P t\' (!(decrypt', 'with noise at most `bootNoise P βk`;\n`Encrypts P t\' (!(decrypt')
        new = R(new, '**Proof sketch.** `bootNAND_eq`, then G3', '**Proof sketch.** `bootNAND_eq` and then G3')
    elif ctl == 3: new = R(new, '  4 ^ (decDepth P + 1) * (2 * (P.columns * β))\n\n', '  4 ^ (decDepth P + 1) * (2 * (β * P.columns))\n\n')
    elif ctl == 4: new = R(new, 'homEvalFormula P (nandFormula P C₁ C₂) evk :=\n  rfl', 'homEvalFormula P (nandFormula P C₁ C₂) evk :=\n  by rfl')
    elif ctl == 5: new = R(new, 'import TCSlib.Complexity.CircuitComplexity.NANDForm\n', 'import TCSlib.Complexity.CircuitComplexity.NANDForm\nimport Mathlib.Data.Nat.Log\n')
    elif ctl == 6:
        b, _ = cut(new); new = R(new, b['bootNoise_le'] + '\n', '')
    elif ctl == 7: new = R(new, '\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW', '\ntheorem ctl_extra : True := trivial\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW')
    elif ctl == 8:
        b, _ = cut(new); h = b['encrypts_bootGate'] + '\n\n'; g10 = b['decrypt_fheEval'] + '\n\n'
        new = R(R(new, h, ''), g10, g10 + h)
    elif ctl == 9: new = R(new, '* `bootNoise_le` (G13): `bootNoise P β ≤', '* `bootNoise_le` (G13): `bootNoise P β  ≤')
elif which == 'Leveled':
    if ctl == 1: new = R(new, 'theorem encrypts_leveledEval (P', 'theorem encrypts_leveledEval  (P')
    elif ctl == 2:
        new = R(new, 'level `Cc.depth` with noise at most `max βin (bootNoise P βk)`:', 'level `Cc.depth` with noise at most `max βin (bootNoise P βk)`;')
        new = R(new, '**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from\n`List.ofFn y`', '**Proof sketch.** We apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from\n`List.ofFn y`')
    elif ctl == 3: new = R(new, '  Fin.append cts fun j => homNot P [cts j]\n\n', '  Fin.append cts (fun j => homNot P [cts j])\n\n')
    elif ctl == 4: new = R(new, 'levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := rfl', 'levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := by rfl')
    elif ctl == 5: new = R(new, 'import TCSlib.Complexity.CircuitComplexity.NANDLayering\n', 'import TCSlib.Complexity.CircuitComplexity.NANDLayering\nimport Mathlib.Data.Nat.Log\n')
    elif ctl == 6:
        b, _ = cut(new); new = R(new, b['decrypt_keygen_leveledEvalCircuit'] + '\n', '')
    elif ctl == 7: new = R(new, '\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW', '\ntheorem ctl_extra : True := trivial\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW')
assert ctl in (None, 0) or new != orig, 'control did not apply'
a, ra = cut(old); b, rb = cut(new)
viol = 0
print(f'== {F}: base {len(a)} declarations, head {len(b)}' + (f' (control {ctl})' if ctl is not None else ''))
for n in sorted(set(a) | set(b)):
    if n not in b: print(f'VIOLATION REMOVED\t{n}'); viol += 1
    elif n not in a:
        if n == HELPER:
            order = [m for m in b if not is_private(b[m])]
            k = order.index(n)
            ok = 0 < k < len(order) - 1 and order[k - 1] == 'encrypts_bootNAND' and order[k + 1] == 'decrypt_fheEval'
            print(f"{'ADDED(public helper, ruled; between G9 and G10)' if ok else 'VIOLATION ORDER'}\t{n}"); viol += not ok
        else:
            ok = is_private(b[n])
            print(f"{'ADDED(private helper)' if ok else 'VIOLATION ADDED'}\t{n}"); viol += not ok
    elif n in TARGETS:
        pa, sa, ha, _ = split_target(a[n]); pb, sb, hb, _ = split_target(b[n])
        if pa != pb: print(f'VIOLATION PROSE\t{n}'); viol += 1
        elif ha != hb: print(f'VIOLATION HEADER\t{n}'); viol += 1
        else: print(f"TARGET(prose and header identical; sketch {'refreshed' if sa != sb else 'unchanged'}; body filled)\t{n}")
    elif a[n] != b[n]: print(f'VIOLATION BODY\t{n}'); viol += 1
    else: print(f'IDENTICAL\t{n}')
doc_start = next((k for k, l in enumerate(ra) if l.startswith('/-!')), -1)
doc_end = next((k for k in range(max(doc_start, 0), len(ra)) if '-/' in ra[k]), -1)
nadded = sum(1 for n in b if n not in a)
blank_budget = nadded
sm = difflib.SequenceMatcher(a=ra, b=rb, autojunk=False)
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == 'equal': continue
    lo, ln = ra[i1:i2], rb[j1:j2]
    indoc = doc_start < i1 and i2 <= doc_end
    adm = op == 'replace' and indoc and any('admitted' in l for l in lo) and len(lo) == len(ln)
    mr = (HELPER is not None and op == 'insert' and indoc and i1 > 0 and ra[i1 - 1].startswith('* `encrypts_bootNAND` (G9)')
          and ln and ln[0].startswith(f'* `{HELPER}`') and all(l.startswith('  ') for l in ln[1:]))
    bl = op == 'insert' and not indoc and all(l.strip() == '' for l in ln) and len(ln) <= blank_budget
    if bl: blank_budget -= len(ln)
    tag = ('TEXT(allowed: module docstring, the admission sentence)' if adm else
           'TEXT(allowed: the ## Main results entry of encrypts_bootGate)' if mr else
           f'TEXT(allowed: blank separator lines of the {nadded} added declarations)' if bl else 'VIOLATION TEXT')
    print(f"{tag}\t{op}\t-{i1+1}..{i2} +{j1+1}..{j2}\t" + ' | '.join(lo + ln)[:200])
    viol += not (adm or mr or bl)
print(f'RESULT violations={viol}')
