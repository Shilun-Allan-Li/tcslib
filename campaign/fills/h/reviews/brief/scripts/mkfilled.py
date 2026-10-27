# Build rvprobe/NTimeHierarchyOverlay2.lean (overlay + ChoiceWords import) and
# rvprobe/NTimeHierarchyFilledA.lean (that, with the review's privates at the home and the proof
# in the body). Every replacement asserted.
import sys, re
W, probe = sys.argv[1], sys.argv[2]
src = open(W + '/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean', encoding='utf-8').read()
lines = src.split('\n')
assert lines[15] == 'import TCSlib.Complexity.TuringMachine.Build.InputRewind'
assert lines[1628] == '' and lines[1627] == 'open Turing' and lines[1726] == '  sorry'
assert lines[1722].startswith('theorem ntime_hierarchy ')
two = lines[:16] + ['import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer',
                    'import TCSlib.Complexity.TuringMachine.ChoiceWords'] + lines[16:]
open(W + '/rvprobe/NTimeHierarchyOverlay2.lean', 'w', encoding='utf-8').write('\n'.join(two))
p = open(probe, encoding='utf-8').read()
a = p.index('/-! ### The route probe\'s lemmas (verbatim) -/')
b = p.index('/-- **The target, over the two contracts.**')
helpers = p[a:b]
helpers = helpers.replace('/-! ### The route probe\'s lemmas (verbatim) -/\n\n', '')
# the route probe's lemmas carry no docstring in the review probe: give each a one-line one
docs = {
 'nh_chain': '/-- The chain\'s induction: `P n ↔ P (n + 1)` for `a ≤ n < b` gives `P a ↔ P b`. -/',
 'nh_absorb': '/-- Finite absorption: a function eventually below `g` is below `F · (g + 1)`. -/',
 'nh_inclusion': '/-- The inclusion `NTIME f ⊆ NTIME (g + 1)` under the domination hypothesis. -/',
 'nh_top': '/-- The top\'s threshold: `C · 2^{C (T + 1)} ≤ 2^{T²}` for every large `T`. -/',
 'nh_bottom': '/-- The bottom\'s threshold: `C₁ (c₀ · fa + 1) ≤ (fa + a + 1)²` once `a ≥ C₁ (c₀ + 1)`. -/',
 'nh_middle': '/-- The middle\'s threshold: `C (C₁ (c₀ · f (n + 1) + 1) + 1) ≤ g n` for every large `n`. -/',
 'nh_stage': '/-- A late stage of a code: some stage of `α` has its bottom rung beyond `N`. -/',
}
for n, d in docs.items():
    pat = re.compile(r'^theorem %s ' % n, re.M)
    assert len(pat.findall(helpers)) == 1, n
    helpers = pat.sub(lambda m: '%s\nprivate theorem %s ' % (d, n), helpers)
for n in ['nh_accepts_of_halts', 'nh_mem_of_accepts']:
    old = '\ntheorem %s ' % n
    assert helpers.count(old) == 1, n
    helpers = helpers.replace(old, '\nprivate theorem %s ' % n)
# variant A truncation: through Turing.run_take_of_halted (ChoiceWords)
oldB = '''    have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
    have hp := NDTM.haltsWithin_iff.mp hT (w.take T) hlen
    have hrun := NDTM.runWith_append (tm := N.tm) (w.take T) (w.drop T) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hp] at hrun
    exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take T, hlen, hp, hrun ▸ hout⟩'''
newA = '''    obtain ⟨hlen, hp, hr⟩ := run_take_of_halted (fun w => N.tm.runWith w (N.tm.initCfg x))
      (fun c => c.state = none)
      (fun w w' h => by simp only [NDTM.runWith_append w w' (N.tm.initCfg x),
        NDTM.runWith_of_halt _ h])
      (NDTM.haltsWithin_iff.mp hT) (w := w) (by omega)
    exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take T, hlen, hp, hr ▸ hout⟩'''
assert helpers.count(oldB) == 1
helpers = helpers.replace(oldB, newA)
oldD = '''length-`T` prefix of the accepting word has halted, and the word runs as that prefix
(`Turing.NDTM.runWith_append` on `w.take T ++ w.drop T`, `Turing.NDTM.runWith_of_halt`), which
therefore accepts. (This variant needs no import beyond region (a)'s; the variant through
`Turing.run_take_of_halted` is `HReviewProbeA.lean`.) -/'''
newD = '''accepting word runs as its length-`T` prefix, which has halted (`Turing.run_take_of_halted`, with
absorption by `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`), so it accepts. -/'''
assert helpers.count(oldD) == 1
helpers = helpers.replace(oldD, newD.replace('accepting word runs', 'accepting word runs', 1))
helpers = helpers.replace("At `t > T`, the\naccepting word runs", "At `t > T`, the\naccepting word runs")
# the body: nh_target's tactic block
c0 = p.index('    NTIME f ⊂ NTIME (fun n => g n + 1) := by\n  obtain ⟨c⟩ := exists_effectiveNDMachineCode')
c1 = p.index('\nend HReview')
body = p[c0 + len('    NTIME f ⊂ NTIME (fun n => g n + 1) := by\n'):c1].rstrip('\n')
filled = list(two)
# home: blank line after `open Turing` (now index 1630); body: the sorry (now index 1728)
assert filled[1630] == '' and filled[1629] == 'open Turing' and filled[1728] == '  sorry'
filled[1728] = body
filled[1630] = '\n' + helpers.rstrip('\n') + '\n'
out = '\n'.join(filled)
out += '\n#print axioms Complexity.ntime_hierarchy\n#print axioms Complexity.ntime_hierarchy_of_pos\n#print axioms Complexity.NTIME_linear_ssubset_square\n'
open(W + '/rvprobe/NTimeHierarchyFilledA.lean', 'w', encoding='utf-8').write(out)
print('ok', len(helpers.split('\n')), len(body.split('\n')))
