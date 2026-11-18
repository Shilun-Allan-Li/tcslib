# mddhAdv_le local hCoinUnwrap candidate

Status: isolated proof-only SCRATCH fragment, NOT natively elaborated/sealed/axiom-checked.
Root's serial freeze audit still owns the one Lean slot. Child ran no Lean/lake/build/Git,
live edit, process operation, extra agent or native search.

Fragment: MddhAdvLeHCoinUnwrap.proof.lean.inc (12 lines). Exactly one tactic block, by plus
four-space body, with no local placeholder/admission/new helper/algorithm or >100-column
line. All other MddhAdvLe.skeleton.lean.inc blocks are unchanged.

## Exact local target and reuse

At arbitrary typed challenge c and rho:B.Coins(kappa), prove
  decide(dlinToMddh(..., List.ofFn rho) = [true])
    = D.distinguisherL(pre(c), coinsCongr hB.coins_eq kappa rho).

hLength is assembled ONLY from existing public readers:
- B.length_ofFn_coins gives |List.ofFn rho| = B.coins.eval(kappa).
- RealizesOn.coins_eq gives B.coins = D.coins; congrArg evaluation transports that equality.
- D.coinLen_eq gives D.coinLen(kappa) = D.coins.eval(kappa).
Thus the actual typed coin list has exactly D's layout length, without opening Coins,
coinLen, RealizesOn, or any machine representation.

Then read dlinToMddh_eq and D.distinguisherL_eq. Use the ALREADY PUBLISHED composite reader
NUPPT.runAt_coinsCongr (explicit A:=B, B:=D), which combines runAt_eq with coinsCongr_ofFn;
do not duplicate that reader's proof or manually reduce a coin equivalence. Finally
List.take_of_length_le hLength.le removes the original reduction's truncation. Both sides
are now the same decide expression on D.runAtL, so rw closes by reflexivity.

Every reduction/machine/coin operation is read through its public theorem. No public
TCSlib or Mathlib definition is passed to simp/rw/unfold; no machine, sampler, decoder,
layout variant, scalar witness or new helper is constructed. The only equality from hB
used HERE is its published coin-polynomial equality; the surrounding hCoinVerdict separately
uses RealizesOn.distinguisherL_eq to connect arbitrary B's actual verdict.
The realisation predicate's layout-length restriction is respected exactly, not weakened.

## Actual static searches and nearest sources

Read the exact local hCoinUnwrap target in MddhAdvLe.skeleton.lean.inc:156-164 and current
SelfReduction.lean:dlinToMddh_eq (:292-297).
Read Asymptotic/Adversary.lean:386-388, exact NUPPT.distinguisherL_eq.
Read Complexity/Randomized/PPT.lean:171 coinLen_eq, :228 length_ofFn_coins,
:249 runAt_eq, :256 coinsCongr, :260 coinsCongr_ofFn, :266 runAt_coinsCongr.
The last is the closest exact reusable activation theorem and is the one actually invoked.
Read Asymptotic/Realization.lean:113 RealizesOn.coins_eq and its self_take consumer :179-183.

rg searched List.take_length/take_of_length_le, length_ofFn_coins, coinsCongr_ofFn and
runAt_coinsCongr/distinguisherL_eq consumers. The exact core list theorem was located/read
at Init/Data/List/TakeDrop.lean:64:
  take_of_length_le (h : l.length<=i) : take i l=l.
Its take_length specialization at :73 is an alternative, but would require an extra
length rewrite; the candidate consumes the more directly applicable bound form.
Pairing/Assumptions.lean:197 is an existing reader-composition parallel; no private proof
or algorithm is copied from it. No new helper exists to probe.

Native checking of the whole ladder and this replacement remains pending. This local
unwrap does not discharge hPreScalar, the two column comparisons or the remaining main
security obligations, and no standard-only completion is claimed.
