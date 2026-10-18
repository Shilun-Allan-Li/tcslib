"""Build the B5a canonizer continuation-4 pre-ship overlay of CodeSimulator.lean.

Usage: python3 -I mkoverlay.py <repo-root> <tools-dir> <out.lean> [<axioms.lean.txt>]

One edit, by a content anchor, asserted (no positional splice): the prescribed home block
(home.lean.txt) is inserted in the blank line between the proof of `exists_canonStripTM` and
the docstring of `exists_canonGrammarStage`. With a fourth argument, its lines are inserted
before `end MachineFormat` as well (the axiom run). The script undoes its edits on its own
output and asserts that this reproduces the input byte for byte, and it asserts that the two
stub statements and the headline are byte-identical to their pinned texts.
"""
import hashlib, sys

root, tools, out = sys.argv[1], sys.argv[2], sys.argv[3]
axioms = open(sys.argv[4], encoding='utf-8').read() if len(sys.argv) > 4 else None
path = f'{root}/TCSlib/Complexity/TuringMachine/CodeSimulator.lean'
src = open(path, encoding='utf-8').read()
home = open(f'{tools}/home.lean.txt', encoding='utf-8').read()

GAP_BEFORE = '      (show 1 ≤ d by dsimp [d]; omega)))\n\n'
DOC = '/-- **The physical grammar stage.** Started on one bank whose tape `header` holds the\n'
anchor = GAP_BEFORE + DOC
assert src.count(anchor) == 1, ('gap anchor', src.count(anchor))
assert src.count(DOC) == 1, ('docstring anchor', src.count(DOC))
assert home.endswith('\n\n') and not home.startswith('\n'), 'home block must end with one blank line'

STAGE = '''private lemma exists_canonGrammarStage (F : MachineFormat) :
    ∃ (m : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (G : MultiTapeTM m Bool S)
      (entry : S) (exit : Bool → S) (a : ℕ) (header : Fin m), Function.Injective exit ∧
      ∀ (x bits rest : List Bool), pairDecode x = some (bits, rest) →
        bits = (codeBitsNat bits).bits →
        canonGuardBlock F * (codeBitsNat bits + 1) ≤ rest.length →
        ∀ d : Cfg m Bool S x, d.state = some entry → d.output = [] →
          d.inputPos.val = 2 * bits.length + 3 →
          d.workTapes header = FinTM.bufferTape bits → d.workTapePos header = 0 →
          (∀ j, j ≠ header → d.workTapes j = FinTM.bufferTape [] ∧ d.workTapePos j = 0) →
          ∃ t ≤ a * (x.length + 1) ^ a,
            (G.runFrom d t).state =
              some (exit (canonGrammar F.k (codeBitsNat bits) rest).isSome) ∧
            (G.runFrom d t).output = [] ∧
            ∀ u < t, ∀ v, (G.runFrom d u).state ≠ some (exit v) := by
  sorry
'''
DECIDER = '''private lemma exists_canonDecider (F : MachineFormat) :
    ∃ (D : FinTM Bool) (a : ℕ), ∀ α : List Bool, ∃ b : Bool,
      D.ComputesInTime α [b] (a * (α.length + 1) ^ a) ∧
        (b = false → F.decode α = F.fallback) ∧
        (b = true → ∃ tail, F.scan α = some tail) := by
'''
HEADLINE = ('theorem exists_polyCanonizer :\n'
            '    ∃ (C : FinTM Bool) (d : ℕ),\n'
            '      C.ComputesFunInTime (fun α => F.serialize (F.decode α)) fun n => d * (n + 1) ^ d := by\n'
            '  obtain ⟨D, a, decider⟩ := exists_canonDecider F\n')
for name, text in [('grammar stage', STAGE), ('decider', DECIDER), ('headline', HEADLINE)]:
    assert src.count(text) == 1, (name, src.count(text))

new = src.replace(anchor, GAP_BEFORE + home + DOC, 1)
TAIL = 'end MachineFormat\n\nend Turing\n'
if axioms is not None:
    assert new.endswith(TAIL) and new.count(TAIL) == 1
    new = new[:-len(TAIL)] + axioms + '\n' + TAIL

back = new
if axioms is not None:
    back = back[:-len(TAIL) - len(axioms) - 1] + TAIL
back = back.replace(GAP_BEFORE + home + DOC, anchor, 1)
assert back == src, 'undoing the edits does not reproduce the input'

open(out, 'w', encoding='utf-8').write(new)
sha = lambda s: hashlib.sha256(s.encode('utf-8')).hexdigest()
print(f'input  {sha(src)}  {src.count(chr(10))} lines')
print(f'home   {sha(home)}  {home.count(chr(10))} lines')
print(f'output {sha(new)}  {new.count(chr(10))} lines')
print('OK: anchored edit(s); stub statements and headline pinned; the undo reproduces the input')
