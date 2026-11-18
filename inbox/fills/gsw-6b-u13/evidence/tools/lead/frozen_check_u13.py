#!/usr/bin/env python3
"""frozen_check_u13.py <repo> <base> <head> [--control N]  (gsw-6b-u13, C4; new, after the 6b
statement delivery's frozen_check6b.py, whose declaration cutter it reuses in spirit).

Checks that in the owned file everything but the regions COMMON §4 permits is byte-identical to
the base:
- every declaration is cut out of the base and head texts (from its doc comment or attribute line
  at column 0, or its declaration line, to the next such start or top-level command);
- for each of the six targets: the doc comment up to `**Proof sketch.**` (the statement prose)
  and the header (keyword through the top-level `:=`, here `:= by`) must be byte-identical; the
  sketch paragraph and the proof body may change;
- every other base declaration (definitions, readers, the instance) must be byte-identical;
- a head declaration not at the base is allowed only if it is `private` (a helper; U13 adds none);
- the non-declaration text (imports, options, namespace, `open`, the module docstring) must be
  identical, except the module-docstring line(s) saying that the targets are admitted.
Controls (--control 1..7) alter the head text in memory and must each report exactly one
violation: 1 a one-character header change; 2 an edit spilling from a sketch into the statement
prose; 3 an edit to a definition's body; 4 an edit to a reader; 5 an unpermitted import; 6 a
deleted target; 7 an unlisted new public declaration. --control 0 compares the base with itself."""
import sys, re, subprocess, difflib
repo, base, head = sys.argv[1:4]
ctl = int(sys.argv[sys.argv.index('--control') + 1]) if '--control' in sys.argv else None
F = 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean'
TARGETS = ['vecMul_secretVector_eq_sum', 'decryptFormula_eval', 'nandFormula_eval',
           'depth_nandFormula_le', 'maxFanin_nandFormula_le', 'decDepth_le']
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
if ctl == 0: new = old
elif ctl == 1: new = new.replace('theorem decDepth_le (P', 'theorem decDepth_le  (P', 1)
elif ctl == 2:
    new = new.replace('same key: `(nandFormula P C₁ C₂).eval', 'same key; `(nandFormula P C₁ C₂).eval', 1)
    new = new.replace('**Proof sketch.** `nandFormula_eq`, `TreeCircuit.neg_eval`',
                      '**Proof sketch.** `nandFormula_eq` and `TreeCircuit.neg_eval`', 1)
elif ctl == 3: new = new.replace('  Matrix.vecMul (decryptColumn P C) (gadget P)\n\n', '  Matrix.vecMul (decryptColumn P C) (gadget  P)\n\n', 1)
elif ctl == 4: new = new.replace('decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := rfl', 'decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := by rfl', 1)
elif ctl == 5: new = new.replace('import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum\n', 'import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum\nimport Mathlib.Data.Nat.Log\n', 1)
elif ctl == 6:
    b, _ = cut(new); new = new.replace(b['decDepth_le'] + '\n', '', 1)
elif ctl == 7: new = new.replace('\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW', '\ntheorem ctl_extra : True := trivial\nend TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW', 1)
assert ctl in (None, 0) or new != git('show', f'{head}:{F}'), 'control did not apply'
a, ra = cut(old); b, rb = cut(new)
viol = 0
print(f'== {F}: base {len(a)} declarations, head {len(b)}' + (f' (control {ctl})' if ctl is not None else ''))
for n in sorted(set(a) | set(b)):
    if n not in b: print(f'VIOLATION REMOVED\t{n}'); viol += 1
    elif n not in a:
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
sm = difflib.SequenceMatcher(a=ra, b=rb, autojunk=False)
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == 'equal': continue
    lo, ln = ra[i1:i2], rb[j1:j2]
    ok = op == 'replace' and doc_start < i1 and i2 <= doc_end and any('admitted' in l for l in lo)
    print(f"{'TEXT(allowed: module docstring, the admission sentence)' if ok else 'VIOLATION TEXT'}\t{op}\t"
          f"-{i1+1}..{i2} +{j1+1}..{j2}\t" + ' | '.join(lo + ln)[:160])
    viol += not ok
print(f'RESULT violations={viol}')
