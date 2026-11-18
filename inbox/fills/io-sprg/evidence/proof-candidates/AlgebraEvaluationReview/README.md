# AlgebraEvaluation review — temporary, NOT_RUN

No Lean/lake/build/cache, source/import changes, git operation, or agent spawn was used.
All replacements and skeletons remain untested. Static name/signature inspection is not
proof elaboration, a kernel check, axiom validation, or seal success.

## Concrete result

`body-map.tsv` covers all 10 current Polys bodies, all 18 current Correctness bodies,
the one proposed support helper, and the efficient-complexity body in Targets. It records
an absolute replacement path, required public helpers, dependency order, and API risks.
The three owners' file hashes are unchanged from the AlgebraEvaluation packet; Degree
and Params have subsequently changed. The current Degree helper signatures inspected
still match their consumers. Current/source packet hashes are in `source-binding.json`.

No false statement, missing positive-kappa premise, or frozen-header repair was found.
The optional-grid zero case, arbitrary prime field, and arbitrary field scaling are
preserved. Existing G1/G2/G3/G4 definitions and all existing theorem headers stay fixed.
There is no existing G2_degrees body to fill and no need to add that theorem.

## Mechanical correction required before use

The packet had 46 local declarations of the form `have h : T` followed by a proof
bullet without an assignment. The root-confirmed single-block repair is `:= ?_`,
then `swap`, before that existing bullet. Fifteen corrected full candidate strings
are in `corrected/`, each staged in a separate tool invocation. Each retains exactly
one lexical outer `by`, no sorry, and line width at most 100. Their `.json` companions
record the original source, repair count, hash, and NOT_RUN status. Unaffected older
bodies remain referenced from the original packets; no candidate has been checked here.

`Polys--prgPoly_degrees-public-card-bound.proof` is the preferred alternate to the
purely mechanical prgPoly repair. It uses the already-imported public
`Finset.card_nsmul_le_sum` at one, `Nat.nsmul_eq_mul`, `Nat.one_le_iff_ne_zero`, and
`MvPolynomial.le_totalDegree`. Hence support cardinality needs no multilinearity,
and the repeated exponent-one calculation disappears from this degree proof. G1_eval
still needs multilinearity to identify the actual monomial evaluation. The alternate
is 46 lines versus 58 in the purely repaired degree body, and remains NOT_RUN.

The norm-rewrite problem reported in Gamma does not occur in this algebra packet.

## Insertion order

1. Degree wrappers, Buckets positions/matrices, SparseFactor reconstruction.
2. Polys slot-count, half degrees, PRG/correction degrees, G3/G4 degrees.
3. Independently Polys halfForm_eval, G1_eval, G3_eval_of_scaled.
4. Correctness selection, packing, oneFlag_bounds; corr-zero and factors; G1-good
   and correction evaluation; successful G2; packed G4 core; sampled full G4; Boolean
   correctness.
5. Add only the specific-G4 support helper in `required-helper-skeleton.lean.txt`,
   with its corrected full proof in corrected/. Put it after eval'_correct and before
   jls_hasComplexity. Inside namespace Params, omit the explicit Params name prefix.
6. Reuse that helper in existing jls_hasComplexity and hasComplexityEff_of_target.

The specific helper is required by the supplied two complexity bodies, not by the
frozen statements themselves. It preserves the literal G4 witness for the target
link. Existential non-efficient complexity alone cannot identify its hidden witness.
The helper's conjunction induction uses existing AllOutputs pure/query readers; no
public conjunction/map helper exists in the currently imported OracleComp API.

## Modularity and size

Current Polys is 398 lines. Direct insertion of original bodies gives 769; repaired
local-have syntax gives 799; choosing the public-card-bound alternate gives 787.
Current Correctness is 262 lines. All bodies plus the proposed helper give 480 before
syntax repair, 496 afterwards. Both remain below 1000. Correctness remains inside the
policy's 150–600 target and needs no split. Polys exceeds the target but is not yet
approaching the mandatory split boundary; its tensor lift/evaluation cluster remains
coherent. No existing declaration or definition needs moving for this packet.

Keep the G4 support helper in Correctness: it depends on that owner's existing
correctness statements and is used by a theorem in the same owner. A new module that
imports Correctness and is then imported back by Correctness would cycle. Likewise,
a new helper module naming Polys.Internal.monomialSlot cannot be imported by Polys.

If final proof debugging pushes Polys toward 1000, a legitimate theorem-only lower
layer is the optional `PolynomialSupport.lean` skeleton. It states the sorted-support
identity directly through list reads, not through the Polys-owned monomialSlot.
Then Polys may import the lower layer and consume monomialSlot_eq. Its four precise
Mathlib roots already occur in the current Polys import closure. It adds no external
import closure, new sampler, machine, encoding, or actual-law change. It would need
facade/collector/seal coverage like every new owner. This is a proposal, not a source
change or a reason to relocate frozen existing declarations. Root can instead keep
these short generic compositions local. Broader foundational helpers reused across
the whole area belong in StructuredSeed/Basic.lean under policy section 1; this
specialized sorted-monomial cluster alone does not require mixing it with the current
fixed-width Boolean list helpers there.

## API verification priorities

- G1_eval: optional indexed-list reads, finite product rewrite orientations, proof
  witnesses on dependent Fin coordinates. Public List.prod_toFinset has the reverse
  orientation needed for the final step, and the packet correctly uses its symmetry.
- halfForm_eval: normalize castSucc/last coordinates with published Fin lemmas if simp
  cannot identify proof witnesses. Fintype.prod_sum is the existing distributivity API.
- G4_eval_sdCore: let-bound inst/first/sd/z may need explicit change steps. Keep the
  empty first-selection branch; no kappa positivity assumption is justified or needed.
- G4_seed_allOutputs: the constructor induction generalizes the two dependent support
  facts. If elaboration objects, root should adjust local proof structure, not strengthen
  the theorem or replace support correctness by a distribution equality.
- Complexity links: use the full dependent jlsSPRG_raw_eq reader plus the derived
  sampler reader. Do not rebuild opaque Raw finite-type instances by reduction.
- There is no new import requirement in the preferred existing-owner route.

Public API source provenance is the exact-manifest mathlib checkout at
/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/packages/mathlib
(029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e), read-only text search, and the managed
worktree. Finset.card_nsmul_le_sum is generated by to_additive from pow_card_le_prod,
Algebra/Order/BigOperators/Group/Finset.lean:199. Nat.nsmul_eq_mul is in
Algebra/Group/Nat/Defs.lean:74; Nat.one_le_iff_ne_zero is Core Init/Data/Nat/Lemmas:145.
All other exact API source lines remain in the original AlgebraEvaluation/APIs.tsv.
