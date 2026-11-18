# Exact LPN scalar-noise law — full untested candidate

01-lpnNoise_law.proof is a complete replacement BODY for existing lpnNoise_law
(LPN.lean:67). It uses the unchanged selector/residue draw and its integer-lift
sample reader. No implementation, import, statement, hypothesis, or algorithm was
changed. No Lean, Lake, build, cache, exact?/apply?, git mutation, or agent spawn
was performed. The proof has not been elaborated; root must validate it and the
resulting dependency/axiom graph. All output files are under /private/tmp.

Source HEAD `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`; LPN.lean SHA256 `162f7692bdc35a09ccb23ef330e2f8d70ca0c2250c5630a99ea6120463ee15f0`.
The context is the existing StructuredSeed namespace before LPNFamily, with
p W : Nat, [NeZero p], [NeZero W], and z : ZMod p.

## Selected existing probability APIs

| API | Exact source | Use |
| --- | --- | --- |
| OneWay.uprob_congr | OneWayFunctions/Basic.lean:50 | Replace this scalar sample event by its pointwise equivalent event. |
| OneWay.uprob_eq_one_div_card | same :144 | A selector or residue hits one fixed point with probability 1/card. |
| HardcoreBit.uprob_prod_and | HardcoreBit/Basic.lean:129 | Independent events on the TWO uniform coordinates multiply exactly. |
| uprob_not | Foundations/Probability.lean:109 | Complement probability is one minus the event probability. |
| Fintype.card_fin | public Mathlib/Core finite-coordinate API | Selector type has cardinal W. |
| ZMod.card | Mathlib/Data/ZMod/Defs.lean:164 | Residue type has cardinal p. |
| lpnNoise_sample | owner LPN.lean:58 | Read the actual integer-lift sampling function without unfolding lpnNoise. |
| Int.cast_natCast | Mathlib/Data/Int/Cast/Basic.lean:60 | Cast the integer lift back into ZMod. |
| ZMod.natCast_zmod_val | Mathlib/Data/ZMod/Basic.lean:197 | Recover the exact canonical residue. |
| mul_inv_rev | Mathlib/Algebra/Group/Defs.lean:1049 | Normalize 1/(W*p) before ring arithmetic. |

All these source modules, including the ring tactic, are in LPN's actual current
import closure; import-closure.json records their presence after following imports
with nested comments/strings removed. No new import or narrowed cache operation is
needed or attempted. The earlier probability search also inspected uprob_prod,
uexp_add, and uexp_indicator, but the selected public exact product theorem makes
rederiving an independence/Fubini identity unnecessary. No generic probability
lemma is proved inline and no count/filter/sum is manually recomputed.

## Exact event calculations

First read the sample and use the public cast round trip to obtain, for every
c : Fin W * ZMod p,

  sample(c) cast back to ZMod p = if c.selector=0 then c.residue else 0.

This is an owner-specific consequence of lpnNoise_sample. It does not reinterpret
or replace the noise's law and never unfolds the LWE.Noise structure definition.

Let qW=1/W and qp=1/p. Existing uniform singleton probabilities give those two
exact values, with their actual finite cardinalities. Explicit local Nonempty
instances are witnessed by zero from the already present NeZero hypotheses;
they add no assumption and ensure the complement law's requirements are clear.

- If z=0, sample(c)=0 iff NOT(selector=0 AND residue!=0). Thus public complement,
  product independence, residue complement and singleton laws give

    Pr[sample=0] = 1 - qW*(1-qp)
                 = 1 - 1/W + 1/(W*p).

- If z!=0, sample(c)=z iff selector=0 AND residue=z. Public independence and the
  two singleton laws give

    Pr[sample=z] = qW*qp = 1/(W*p).

The logical equivalences are proved by the two cases of the actual selector; no
new probability identity, disjoint-union principle, conditioning construction,
or sampler is introduced. The final equalities use public inverse normalization
and ring distributivity, not a reproof of finite probability algebra.

## Boundaries, assumptions, and pending validation

Only p!=0 and W!=0 are used, exactly as in the existing statement. Primality,
W>1, p>1, schedule growth, and any asymptotic claim are unnecessary. At W=1 the
selector is always zero, so both cases reduce to the uniform residue probability
1/p. At p=1 only z=0 exists; its right-hand side is 1-1/W+1/W=1. The zero-residue
calculation is valid for that singleton type too. There is no empty sample space.

No local CoinContract/UniformSampler value, efficiency proof, or probability notion
was constructed. The candidate uses no current sorry body or downstream result
as evidence; its only owner result is the already-proved lpnNoise_sample reader.
It contains one outer tactic block and bullet subgoals, no nested tactic block,
new helper declaration, placeholder, or new import. The existing theorem's proof
sketch remains applicable: exact selector/residue independence supplies the law.

Remaining mechanical risks are rewrite occurrence inference in uprob_congr/not,
instantiation of the forall residue singleton equation, and simplification of the
integer-to-residue coercion. The selected API signatures were read directly; this
source review is not a successful kernel test. No exact?/apply? output is claimed.
reuse-searches.json records the exact text searches, static-checks.json the source
binding and text metrics, and SHA256SUMS the packet digests.
