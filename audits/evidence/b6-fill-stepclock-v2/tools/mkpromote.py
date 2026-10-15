"""Apply the B6-F1 v2 promotions to Build/CounterLoop.lean and SymbolLift.lean, every edit asserted.

Usage: python3 -I mkpromote.py <repo-root> <tools-dir> <out-CounterLoop.lean> <out-SymbolLift.lean>

CounterLoop.lean, eight edits:
  P1–P3  `private lemma` -> `lemma` on `counter_dec_spec`, `counter_dec_zero`,
         `counter_word_decrement` (visibility only; name, statement, proof, docstring kept);
  H1     cl-decrement.lean.txt at the blank line after `decrementTM_run_underflow_ofCfg`;
  H2     cl-counterWord.lean.txt at the blank line after `counterWord`'s definition;
  H3     cl-counterOverhead.lean.txt at the blank line after `counterOverhead`'s definition;
  H4     cl-lastEmb.lean.txt at the blank line after `lastEmb`'s definition.
SymbolLift.lean, one edit:
  H5     sl-fields.lean.txt at the blank line before `end Overlay`.
Each output, with the inserted blocks removed and `private ` restored, is checked to be the
input byte for byte."""
import sys, hashlib

root, tools, out_cl, out_sl = sys.argv[1:5]
P = f'{root}/TCSlib/Complexity/TuringMachine'
read = lambda p: open(p, encoding='utf-8').read()
block = lambda n: read(f'{tools}/{n}').rstrip('\n').split('\n')
sha = lambda s: hashlib.sha256(s.encode('utf-8')).hexdigest()

def one(L, pred, what):
    idx = [i for i, l in enumerate(L) if pred(l)]
    assert len(idx) == 1, (what, idx)
    return idx[0]

# ---- CounterLoop
src = read(f'{P}/Build/CounterLoop.lean'); L = src.split('\n')
promos = ['counter_dec_spec (w : List Bool) :', 'counter_dec_zero (w : List Bool) :',
          'counter_word_decrement (w : List Bool) (r : ℕ)']
pidx = []
for p in promos:
    i = one(L, lambda l: l == 'private lemma ' + p, p); pidx.append(i)
# homes: (index of the blank line, the line before it, the line after it, block)
def home(before_pred, before_what, after_check, name):
    b = one(L, before_pred, before_what)
    if after_check is None:
        # anchored on the line after the home: the home is the blank line before it, and the
        # line before the home closes `decrementTM_run_underflow_ofCfg`
        h = b - 1
        assert L[h - 1] == '  · simpa only [counter_decrement_run, Cfg.mapWorkSymbols] using hh'
        assert L[h] == '', (name, 'home not blank', L[h])
        return h, name
    h = b + 1
    assert L[h] == '', (name, 'home not blank', L[h])
    assert after_check(L[h + 1]), (name, 'after', L[h + 1])
    return h, name
homes = [
  home(lambda l: l == '/-! ## Counter arithmetic -/', 'arithmetic section', None,
       'cl-decrement.lean.txt'),
  home(lambda l: l == '  (fun u => (decFixed u).getD u)^[r] w', 'counterWord body',
       lambda l: l.startswith('/-- The cost sum of the first `r` decrements'), 'cl-counterWord.lean.txt'),
  home(lambda l: l == '  ∑ j ∈ Finset.range r, (2 * ((counterWord w j).takeWhile not).length + 2)',
       'counterOverhead body', lambda l: l.startswith('/-- A borrow either detects'), 'cl-counterOverhead.lean.txt'),
  home(lambda l: l == '  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩', 'lastEmb body',
       lambda l: l.startswith('/-- Run a rich-alphabet body'), 'cl-lastEmb.lean.txt'),
]
N = list(L)
for i in pidx:
    assert N[i].startswith('private lemma ')
    N[i] = N[i][len('private '):]
inserted = {}
for h, name in sorted(homes, reverse=True):
    blk = block(name); inserted[name] = (h, len(blk))
    N = N[:h] + [''] + blk + [''] + N[h + 1:]
out = '\n'.join(N)
# reverse check
back = list(N)
for name in [n for _, n in sorted(homes, reverse=True)]:
    blk = block(name)
    s = '\n'.join(back)
    piece = '\n' + '\n'.join(blk) + '\n\n'
    assert s.count(piece) == 1, name
    s = s.replace(piece, '\n', 1)
    back = s.split('\n')
for p in promos:
    i = one(back, lambda l: l == 'lemma ' + p, p)
    back[i] = 'private ' + back[i]
assert '\n'.join(back) == src, 'CounterLoop reverse check failed'
open(out_cl, 'w', encoding='utf-8').write(out)
print(f'CounterLoop.lean: {len(L)} lines, sha256 {sha(src)}')
for p, i in zip(promos, pidx):
    print(f'  promoted (visibility only) line {i + 1}: lemma {p.split(" ")[0]}')
for h, name in sorted(homes):
    print(f'  home line {h + 1} (blank): {name}, {len(block(name))} lines')
print(f'  overlay: {len(N)} lines, sha256 {sha(out)}')

# ---- SymbolLift
src = read(f'{P}/SymbolLift.lean'); L = src.split('\n')
e = one(L, lambda l: l == 'end Overlay', 'end Overlay')
h = e - 1
assert L[h] == '', ('SymbolLift home not blank', L[h])
assert L[h - 1] == '  · simp [Cfg.liftOver, Cfg.decodeSymbols, Cfg.liftSymbols]', L[h - 1]
blk = block('sl-fields.lean.txt')
N = L[:h] + [''] + blk + [''] + L[h + 1:]
out = '\n'.join(N)
back = N[:h] + [''] + N[h + 1 + len(blk) + 1:]
assert '\n'.join(back) == src, 'SymbolLift reverse check failed'
open(out_sl, 'w', encoding='utf-8').write(out)
print(f'SymbolLift.lean: {len(L)} lines, sha256 {sha(src)}')
print(f'  home line {h + 1} (blank, before `end Overlay`): sl-fields.lean.txt, {len(blk)} lines')
print(f'  overlay: {len(N)} lines, sha256 {sha(out)}')
