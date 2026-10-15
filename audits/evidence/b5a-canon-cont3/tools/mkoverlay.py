"""Build the B5a canonizer continuation-3 pre-ship overlay of CodeSimulator.lean.

Usage: python3 -I mkoverlay.py <repo-root> <tools-dir> <out.lean>

Two edits, both by content anchors, both asserted (no positional splice):
  1. the prescribed home block (home.lean.txt) is inserted in the gap between
     `exists_canonParseFront` and the docstring of `exists_polyCanonizer`;
  2. the headline's `sorry` body is replaced by the proved glue (headline.lean.txt),
     whose first three lines must be the frozen signature, byte for byte.
The script then undoes both edits on its own output and asserts that this
reproduces the input byte for byte.
"""
import hashlib, sys

root, tools, out = sys.argv[1], sys.argv[2], sys.argv[3]
path = f'{root}/TCSlib/Complexity/TuringMachine/CodeSimulator.lean'
src = open(path, encoding='utf-8').read()
home = open(f'{tools}/home.lean.txt', encoding='utf-8').read()
glue = open(f'{tools}/headline.lean.txt', encoding='utf-8').read()

GAP_BEFORE = '    exact ready (of_decide_eq_true yes)\n\n'
DOC = '/-- **A polynomial-time canonizer** (spec, fill pending — batch B5a): one finite\n'
anchor = GAP_BEFORE + DOC
assert src.count(anchor) == 1, ('gap anchor', src.count(anchor))
assert src.count(DOC) == 1, ('docstring anchor', src.count(DOC))
assert home.endswith('\n\n') and not home.startswith('\n'), 'home block must end with one blank line'

SIG = ('theorem exists_polyCanonizer :\n'
       '    ∃ (C : FinTM Bool) (d : ℕ),\n'
       '      C.ComputesFunInTime (fun α => F.serialize (F.decode α)) fun n => d * (n + 1) ^ d := by\n')
BODY = SIG + '  sorry\n'
assert src.count(BODY) == 1, ('headline anchor', src.count(BODY))
assert glue.startswith(SIG), 'the glue must start with the frozen signature'
assert glue.endswith('\n') and 'sorry' not in glue, 'the glue is complete and admission-free'

new = src.replace(anchor, GAP_BEFORE + home + DOC, 1)
assert new.count(BODY) == 1
new = new.replace(BODY, glue, 1)

# Undo both edits on the output and compare with the input.
back = new.replace(glue, BODY, 1).replace(GAP_BEFORE + home + DOC, anchor, 1)
assert back == src, 'undoing the two edits does not reproduce the input'

open(out, 'w', encoding='utf-8').write(new)
sha = lambda s: hashlib.sha256(s.encode('utf-8')).hexdigest()
print(f'input  {sha(src)}  {src.count(chr(10))} lines')
print(f'home   {sha(home)}  {home.count(chr(10))} lines')
print(f'glue   {sha(glue)}  {glue.count(chr(10))} lines')
print(f'output {sha(new)}  {new.count(chr(10))} lines')
print('OK: two anchored edits; the undo reproduces the input byte for byte')
