"""landedits.py <head file> <base file> <out file>: the review's drafted landing edits, each asserted.
Group A (docstrings/comments): A1 BF's docstring restored to the base and its dependency clause
updated; A2 the module status; A3 the target's status label and an Implementation paragraph in place
of the stale obligations list; A4 the home's header without campaign labels; A5-A7 proof sketches.
Group B (proof text, rule 10): B1-B3 the coordinate simps take the published cast route (`simp only`, the sealed run's lemmas).
Group C (optional lint cleanup, proof text): unused simp arguments and no-op push_casts."""
import sys
head, base, out = sys.argv[1:4]
t = open(head, encoding='utf-8').read()
b = open(base, encoding='utf-8').read()
def rep(old, new, count=1):
    global t
    assert t.count(old) == count, (t.count(old), old[:80])
    t = t.replace(old, new)
def line(n, old, new):
    global t
    L = t.split('\n')
    assert L[n - 1] == old, (n, L[n - 1])
    if new is None: del L[n - 1]
    else: L[n - 1] = new
    t = '\n'.join(L)
# Group C and B first (line-numbered, bottom-up so numbers stay valid)
line(1491, '        · exact un_buffer_ge _ _ (by push_cast at hq ⊢; omega)', '        · exact un_buffer_ge _ _ (by omega)')
line(1488, '        rw [if_neg (by push_cast at hq ⊢; omega)]', '        rw [if_neg (by omega)]')
line(1417, '        push_cast', None)
line(1400, '      push_cast', None)
line(1186, '        · exact un_buffer_ge _ _ (by push_cast at hq ⊢; omega)', '        · exact un_buffer_ge _ _ (by omega)')
line(960, '      simp [Fin.coe_natAdd, hup]', '      simp only [Fin.coe_natAdd, hup, zero_add]')
line(782, '    simp [jEx, Fin.coe_cast, Fin.coe_natAdd, hup]', '    simp only [jEx, Fin.coe_cast, Fin.coe_natAdd, hup, zero_add]')
line(780, '    simp [jBuf, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, hup]',
     '    simp only [jBuf, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, hup, Fin.val_eq_zero, add_zero]')
line(662, '    exact Fin.ext (by simp [Fin.val_one])', '    exact Fin.ext (by simp)')
line(615, '        simp only [un_inRewTM, Fin.reduceEq, ↓reduceIte]', '        simp only [un_inRewTM, ↓reduceIte]')
line(475, '          rw [show (L : ℤ) - r = ((L - r : ℕ) : ℤ) by push_cast; omega,', '          rw [show (L : ℤ) - r = ((L - r : ℕ) : ℤ) by omega,')
line(460, '        simp only [un_bankTM, Fin.reduceEq, ↓reduceIte]', '        simp only [un_bankTM, ↓reduceIte]')
# A1: BF's docstring = the base's, then its dependency clause updated
ho = 'time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to\nestablish a hierarchy theorem"]; spec, fill pending — phase P3.3): a\n'
bo = 'time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to\nestablish a hierarchy theorem"]): a\n'
assert b.count(bo) == 1
rep(ho, bo)
hf = ('`Turing.ndAcceptsWithin_decider_of_universal`. Fill obligation, named: `E`\n'
      'itself (iterative deepening over the choice words of the fixed `UN`, each\n'
      'replayed by its replay machine under the step-clocked runner, with a window\n'
      'clear between replays; no `|x|` term). The proof applies\n')
bf = ('`Turing.ndAcceptsWithin_decider_of_universal`. `E` itself is\n'
      '`Turing.FinNDTM.exists_exhaustiveDecider`, proved (iterative deepening over the\n'
      'choice words of the fixed `UN`, each replayed by its replay machine under the\n'
      'step-clocked runner, with a window clear between replays; no `|x|` term), so the\n'
      "decider's only open dependency is the universal NDTM. The proof applies\n")
assert b.count(bf) == 1
rep(hf, bf.replace("decider's only open dependency is the universal NDTM. The proof applies\n",
                   "decider's only open dependency is the universal NDTM's interpreter core\n"
                   "`Turing.exists_ndInterpreterCore`. The proof applies\n"))
# A2: the module status
rep('**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` and the hierarchy\n'
    '`Complexity.ntime_hierarchy` are sorried; the exponential decider and the two corollaries are\n'
    'proved from them.\n',
    '**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` is proved from the\n'
    'interpreter core `Turing.exists_ndInterpreterCore` (sorried in\n'
    '`TCSlib.Complexity.TuringMachine.NDCodeSimulator`); the hierarchy `Complexity.ntime_hierarchy`\n'
    'is sorried; the exponential decider and the two corollaries are proved from them.\n')
# A3: the target's docstring
rep('/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];\n'
    'decision CH34-Q8; spec, fill pending — phase P3.3): for every effective\n',
    '/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];\n'
    'decision CH34-Q8): for every effective\n')
rep('`O(t + 1)`. Fill obligations, named: the startup and per-code installation;\n'
    "the choice writer's bounded contract; the window copy; the interpreter core\n"
    "(H1's hosted clock over the step block at three work tapes, harvested with\n"
    "H2's promotion); the guess-then-run assembly; the `C`-ledger per code. -/\n",
    '`O(t + 1)`.\n\n'
    '**Implementation.** The setup before the guess is one seam chain of eight phases: the prefix\n'
    'canonizer `Turing.prefixCanonTM` with the first-component extractor, embedded silently with its\n'
    'output `bits t` captured on a scratch tape; the code buffer\'s rewind and clear; an erase of the\n'
    "extractor's scratch tapes that also rewinds the capture; the expansion of `bits t` into the\n"
    "unary block (`Turing.expandTM`); the block's rewind; the counter's clear; and the input rewind.\n"
    'It first reaches its exit within `(7·|α| + 130)·(t + 1)` steps, with no `|x|` term, so the\n'
    'constant is `C = C_P + C_R + 13` with `C_P = 7·|α| + 130` and `C_R` the core\'s. -/\n')
# A4: the home's header
rep("/-! ### The setup machine's pieces (continuation UN cont1)\n\n"
    '`un_universal_of_setup` above reduces target 1 to its setup hypothesis. The setup built below\n',
    "/-! ### The setup machine's pieces\n\n"
    '`un_universal_of_setup` above reduces `Turing.exists_timed_universal_NDTM` to its setup\n'
    'hypothesis. The setup built below\n')
# A5-A7: proof sketches
rep('`pairEncode (pairEncode a b) x`, halts at exactly `3·|pairEncode a b| + 4 + (4·|a| + 5)` and is\nlive before. -/\n',
    '`pairEncode (pairEncode a b) x`, halts at exactly `3·|pairEncode a b| + 4 + (4·|a| + 5)` and is\nlive before.\n\n'
    '**Proof sketch.** `Turing.prefixCanon_run` at the extractor\'s halting time, read through\n'
    '`Turing.prefixCanonTM_eq` and `Turing.FinTM.pairExtractTM_fst_run`, gives the halt. Before the\n'
    "parser's `3·|pairEncode a b| + 4` steps the run is live by `Turing.prefixCanon_start`; after\n"
    "them it is the extractor's run, live before its own halt. -/\n")
rep('earlier, with the bank blank, the bank and guide heads at the origin, the guide\'s word and\neverything else unchanged. -/\n',
    'earlier, with the bank blank, the bank and guide heads at the origin, the guide\'s word and\neverything else unchanged.\n\n'
    '**Proof sketch.** After `r ≤ L + 1` steps the selected cells right of `L − r` are blank and the\n'
    'bank and guide heads are at `L − r`, by induction on `r`: the first step is unconditional, and\n'
    'for `1 ≤ r ≤ L` the guide still reads a symbol of its word. At `L + 1` the guide reads the blank\n'
    'left of its word, so the last step moves right into the park; before it the state is `0` or\n'
    '`1`. -/\n')
rep('exactly `p + 1` and not earlier, with the input head at `1` and every other field unchanged. -/\n',
    'exactly `p + 1` and not earlier, with the input head at `1` and every other field unchanged.\n\n'
    '**Proof sketch.** After `r ≤ p` steps the input head is at `p − r` in the scan state, by\n'
    'induction on `r`: the first left step is unconditional, and at every later position `≥ 1` the\n'
    'head reads an input symbol. At `0` it reads the left blank and moves right into the park at\n'
    '`1`; before that the state is `0` or `1`. -/\n')
assert all(len(l) <= 100 for l in t.split('\n')), [l for l in t.split('\n') if len(l) > 100]
open(out, 'w', encoding='utf-8').write(t)
print('landing edits applied: A1-A7, B1-B3, C (9 lint lines)')
