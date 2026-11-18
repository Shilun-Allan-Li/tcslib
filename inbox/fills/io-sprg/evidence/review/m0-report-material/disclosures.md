## Quantifier audit and pre-M0 refinements

The statements are not yet frozen. These are disclosed design choices and the
resolved user ruling, not post-M0 statement changes. No weakening is hidden.

| Choice / location | Exact scope and reason |
| --- | --- |
| SP-W1: rational delta (`Params.lean:52`; raw/efficient existence binders) | The user's exact ruling is: “Use rational δ throughout, coercing it to real values for analysis”. Params stores `delta : Q` in (0,1); rounded real-power definitions and E0 receive its real coercion. No theorem quantifies over arbitrary uncomputable real construction data. The initial arbitrary-real counterexample is resolved by this ruling. |
| Faithful generic encodings (`BoolPRG`, `SPRG.Raw`) | Supplied index/draw encodings have injectivity fields, and finite equivalences/cardinalities are explicit data. This strengthens the input representation contract. It prevents hidden index or draw information from being erased by a constant code. The user authorized best judgment on these pre-M0 refinements. Shared `SamplesEfficiently` does not imply injectivity or computability of its abstract equivalence; do not conflate these facts. |
| Complete parameter words (LPN `sampleWord`, sPRG `idWord`/`sdWord`) | Prime first and explicit unary dimension/security parameter avoid collisions forcing a single `UniformSampler.Omega(y)` to stand for incompatible draw dimensions. The full typed public input determines draw and core encodings; no machine computes a prime. |
| Optional bucket grid positions (`Buckets.indexMap`) | At kappa=0, rc=0 while m(0) may be nonzero. A total `Fin m -> Fin rc x Fin rc` is impossible. `Option` with `none` on overfull/empty grids preserves all good placements and the settled exact capacity. Correction polynomials sum assigned coordinates and use zero for `none`. |
| Deterministic sparse factors (`SparseFactor`) | The paper leaves a valid factor choice unspecified. Row-major listing and zero padding give honest deterministic cores with no classical enumeration. The success-conditioned factorization statement is unchanged. |
| Explicit term syntax (`PolyTerms`) | `List (R x List sigma)` uses repeated variables for powers. Existing `BoolCircuit.encodeList` with pair delimiters encodes variable-length components. It denotes actual composite polynomials, not an opaque source code chosen after each parameter. |
| Encoding module split | The encoding portion of the planned Samplers module lives in `Encoding.lean`; it depends only on Params and existing equivalence roots. This is a disclosed modular split, not additional Phase B functionality. |
| Canonical assumption challenges | Mandatory reuse wins: `lpnEnc` is exactly existing `LWE.encodeChallenge` at the family's width, and `prgEnc` exactly `G.challengeStr`. Prime-first applies to the new construction challenges and reduction advice. This interpretation was explicitly selected and recorded before M0. |
| Actual assumption families | Raw/efficient existence only assume LPN for the E-indexed construction families built from the supplied G, representation, and rational delta. This is Q-S1 / Dv3, not a literal Def.2.3 bridge or an assumption for all unrelated LPN families. |
| Raw existence realisability scope (`Security`) | `hR` quantifies over the supplied data's E-indexed Params. It need not cover every unrelated Params. This reduces a sufficient hypothesis and strengthens the conditional raw existence statement. Efficient existence retains `hT : forall P : Params, P.Targets` as proposed. Record the distinction explicitly. |
| Advice bounds | PRG uses explicit coefficient 100; LPN uses the deliberately coarser 4096 to cover its extra nested complete-draw/list fields. Both are concrete syntactic PolyExpr bounds at all independent dimensions, not eventual or existential advice-polynomial claims. |
| Layout-only shared RealizesOn / Dv16 | Each universal-realiser inequality constrains realisers only on encoded challenges and coin strings of the declared layout length. This weaker predicate admits more realisers, making every-realiser security inequalities stronger. All uses are shared API, no local variant. |
| Subexponential security / Dv13 | Advantage against NUPPT has fixed exponent `min(E*cL,min(E*D*cG,1))/2`; assumption exponents precede all adversaries. The theorem is not about subexponential-time adversaries. |
| Exact and eventual bounds / Dv7 | prop41 and hop bounds are for every kappa. Claim4.2 and stretch state common eventual thresholds. Claim4.2's threshold precedes all public primes. Rounding and zero-parameter cases remain total. |
| Raw vs primitive / Dv18 | Raw security/correctness/stretch contain explicit algorithms without an unproved efficiency assertion. The only new primitive values are target assemblies with mandatory named field bridges. T1-T6 remain propositions with the exact Phase B notice, never unconditionally inhabited. |

The final independent review found no fidelity/efficiency quantifier blocker in its
snapshot. In particular, prop41 chooses both advice families before every realiser
and every kappa; T1/T2 maps precede every pp; T4 maps precede every schedule; T6 uses
`SamplesEfficiently (P := fun _ => PrimeSchedule)` so ONE U/c/f precedes all schedules.
Assembly restricts its witnesses to fixed schedule/Unit while retaining those same
uniform objects. T3 and T5 are joined only on their matching complete draw types.

At M0, named sorried field proofs can make Raw/primitive definitions and instances
transitively depend on `sorryAx`. The actual axiom census must report this graph.
The permitted syntactic placement of holes in named theorem bodies does not imply
that only theorem constants have `sorryAx` dependencies.
