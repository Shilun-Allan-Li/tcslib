# Build rvprobe/HChainProbe.lean (the staged chain probe for D1 (A)): the route probe's seven
# lemmas verbatim (with their docstrings), then the review probe's additions with the truncation
# through Turing.run_take_of_halted, nh_target and the walk; sealed over 12. Asserted.
import sys
W = sys.argv[1]
route = open(W + '/rvprobe/HRouteProbe.lean', encoding='utf-8').read()
rev = open(W + '/rvprobe/HReviewProbe.lean', encoding='utf-8').read()
a = route.index('/-- **The chain\'s induction.**')
b = route.index('\nend HRoute')
lemmas = route[a:b].rstrip('\n')
c = rev.index('/-! ### The review\'s additions -/')
d = rev.index('\nend HReview')
adds = rev[c:d].rstrip('\n')
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
assert adds.count(oldB) == 1
adds = adds.replace(oldB, newA)
oldD = '''**Proof sketch.** At a length `t ≤ T`, pad (`Turing.FinNDTM.AcceptsWithin.mono`). At `t > T`, the
length-`T` prefix of the accepting word has halted, and the word runs as that prefix
(`Turing.NDTM.runWith_append` on `w.take T ++ w.drop T`, `Turing.NDTM.runWith_of_halt`), which
therefore accepts. (This variant needs no import beyond region (a)'s; the variant through
`Turing.run_take_of_halted` is `HReviewProbeA.lean`.) -/'''
newD = '''**Proof sketch.** At a length `t ≤ T`, pad (`Turing.FinNDTM.AcceptsWithin.mono`). At `t > T`, the
accepting word runs as its length-`T` prefix, which has halted (`Turing.run_take_of_halted`, with
absorption by `Turing.NDTM.runWith_append` and `Turing.NDTM.runWith_of_halt`), so it accepts. -/'''
assert adds.count(oldD) == 1
adds = adds.replace(oldD, newD)
tail = rev[d:]
assert tail.startswith('\nend HReview')
head = '''/-
H's chain probe (review sub-agent, 2026-10-27; for staging as `HChainProbe.lean.txt`): the route
probe's seven lemmas verbatim, the truncation through the shared `Turing.run_take_of_halted`, and
the target's statement proved over the two contracts (`nh_target`), sealed over the twelve
other-file definitions the chain reads, with the axiom walk. A probe record; its lemmas and the
body of `nh_target` may be copied into the fill's home as `nh_` privates and the target's body.
-/
import TCSlib.Complexity.Diagonalization.NTimeHierarchy
import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer
import TCSlib.Complexity.TuringMachine.ChoiceWords

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Turing

section HChain

attribute [local irreducible] NTIME FinNDTM.DecidesInTime FinNDTM.AcceptsWithin NDTM.HaltsWithin
  NDTM.runWith NDTM.initCfg NTimeDiag.ladder NTimeDiag.budget NTimeDiag.stage
  NTimeDiag.stageCode TimeConstructible CodeNDTM.toFinNDTM

'''
tail = tail.replace('\nend HReview', '\nend HChain', 1)
out = head + lemmas + '\n\n' + adds + '\n' + tail
out = out.replace('/-! ### The review\'s additions -/\n\n', '')
open(W + '/rvprobe/HChainProbe.lean', 'w', encoding='utf-8').write(out)
print('ok', out.count('theorem nh_'))
