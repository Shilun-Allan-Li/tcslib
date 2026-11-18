# Algebra evaluation and specific-G4 complexity candidates — NOT RUN

Prepared against d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3. All files are temporary
proof text. No Lean/lake/build/cache, source/import changes, git mutation, or spawn.
No elaboration, exact?/apply?, kernel, axiom, or seal success is claimed. The source
hashes, public API source positions, import closure, and textual checks are recorded.

There are 19 NEW complete strings: eight existing Polys bodies; nine existing
Correctness bodies; one proposed theorem-only Correctness helper; and one existing
Targets body. Each has one outer tactic block, no explicit placeholder, and width
at most 94. They depend on the actual upstream mathematics, including currently
unproved Degree/Buckets/SparseFactor obligations. Using a sorried dependency to
elaborate a candidate would not validate that dependency or these conclusions.

## Coverage and insertion order

inventory.tsv maps all ten existing Polys nonreader obligations, all eighteen
existing Correctness obligations, the proposed helper, and the efficient-complexity
link. Eleven older bodies are referenced and hashed rather than duplicated:
../Polys has G3/G4 degrees; ../Correctness has eight simple selection/packing/bounds
bodies; ../SelectionFinal has the previously missing firstGood_some_minimal body.
Thus there is no remaining unstaged existing Polys/Correctness body in this index.

1. Prove the shared Degree wrappers, Buckets and SparseFactor interfaces first.
2. Polys: slot-count, half-form degrees, PRG/correction degrees, G3/G4 degrees;
   independently halfForm_eval, G1_eval, G3_eval_of_scaled.
3. Correctness: selection/packing/oneFlag; corr_zero; one-instance factors;
   good G1 and correction evaluation; successful G2; packed G4 core evaluation;
   full-law G4 support; Boolean eval correctness.
4. Add the proposed Params.G4_seed_allOutputs THEOREM ONLY after eval'_correct.
5. Reuse it in jls_hasComplexity and Params.hasComplexityEff_of_target. The latter
   candidate supersedes ../Targets/06-hasComplexityEff_of_target.PARTIAL.lean.txt;
   that older file remains an explicitly historical partial candidate.

There is no G2_degrees declaration in the current source. No new one is needed:
G2_eq, G1_eq, prgPoly_degrees false, correctionPoly_degrees false, and the addition
bounds yield its bidegrees if a downstream local step ever needs them. No invented
source obligation or statement change is included here.

## Actual algebra, including the tensor split

halfForm_eval proves each linear functional at the augmented secret first. The
last coordinate gives b_i and the earlier coordinates give -A_i*s; padding gives
one. Fintype.prod_sum is the existing finite distributive expansion, so no generic
tensor expansion is reproved.

G1_eval uses the actual sorted support, not an assumed tensor-slot lemma. For a
support monomial, supplied multilinearity and nonzero exponents give exponent one.
The supplied total-degree bound gives support.card <= d <= D+D. The two halves
are joined by Fin.prod_univ_add; Fin.prod_univ_eq_prod_range/prod_subset remove
padding; Fin.prod_univ_fun_getElem/List.prod_toFinset and sort_toFinset recover
the support product; exponent one identifies the original eval₂ monomial.
The same local exponent/cardinality bookkeeping occurs in prgPoly_degrees. This
repetition is disclosed; searches found no public matching support-cardinality
lemma for this representation. Root may factor a theorem-only local helper later,
after the required overlap probes, instead of silently treating the two local
calculations as distinct generic infrastructure.

corr_zero_of_not_bad reuses eval₂Hom_congr' on the actual variable set, then
casts the supplied R.eval_poly with eval₂_comp. Sparse reconstruction is the
existing sparseFactor_mul_of_card_le, with bucketMatrix_nonzero_card_le and
success bounds. correctionPoly_eval_oneSd reads the actual optional position and
uses Matrix.mul_apply plus bucketMatrix_apply_indexMap. G2 cancellation is ring
algebra; G3 scaling factors the precomputed private scaled copy. G4 reads the
actual explicit public/private sum equivalence via eval_rename, reads packSeed
coordinates, and keeps only the selected successful instance.

The G4 core proof handles kappa=0: firstGood is none, all active flags vanish,
and the empty sum is zero. No positivity, nonempty repetition, fixed prime,
noise-rate estimate, or asymptotic assumption is added to any algebra statement.

## One shared specific-G4 support helper

The proposed theorem asserts exactly that every sdSamp' seed evaluates G4 to the
field encoding of eval'. It preserves the SPECIFIC witness required by T2;
jls_hasComplexity's existential alone cannot identify its hidden witness with G4.

The imported Games API has no AllOutputs.and or AllOutputs.map. The helper joins
G4_eval_eq and eval'_correct once by a local constructor induction, explicitly
rewriting allOutputs_pure/query at BOTH hypotheses and the goal. This is novel
specific-support logical glue, not an unfolded foreign AllOutputs definition.
The final sdSamp' map uses its owner reader, map_eq_bind and AllOutputs.bind/pure.
No forbidden Games.Closeness or CoinSampling helper is imported.

Both complexity bodies then select G4, read the FULL jlsSPRG_raw_eq, transport
jlsSPRG_raw_sdSamp through that same full reader, rewrite the sampler equality,
and reuse G4_seed_allOutputs. No duplicate pointwise Boolean/field proof remains.
The efficient link also reuses the ONE f supplied by qGenTarget before all
parameters; it proves no efficiency target and constructs no machine or sampler.

## Precise remaining verification concerns

All bodies are untested strings. The main likely mechanical adjustments are:

- dependent Fin proof/cast normalization in last/castSucc tensor coordinates;
- optional-list getElem syntax and finite product rewrite orientation in G1;
- implicit type parameters for weighted-degree C/X applications;
- let-bound structured coordinates when applying the packed-coordinate readers;
- induction generalization of the two support facts in the proposed helper;
- dependent record and derived sampler transport in the two complexity bodies.

These are isolated syntax/elaboration risks, not claims that a checked body
exists. There is no identified false statement or missing mathematical premise.
If dependent transport needs more annotations, retain the same full-record and
sampler readers; do not unfold foreign definitions. Core/Mathlib definitions are
never passed to simp/rw/unfold; only public lemmas and local lets are used.

## Reuse and import audit

APIs.tsv records public source positions. reuse-searches.json records actual text
searches and their results. exact?/apply? and the required Rule10 seals remain
root-owned and pending. The ../OverlapProbes packet supplies goals whose imports
exclude all M0 constants, preventing a sorried theorem from matching itself.

The comment/string-aware source import audit includes the `import all` syntax in
Batteries; toolchain Init/Lean/Std modules are terminal external nodes. Every
required public Mathlib/TCSlib module is in the present owner closure. No new
Mathlib root, broad import, algorithm definition, efficiency proof, global
attribute, or implementation source edit is proposed. Closure counts are not
direct cache-root counts and are not evidence of elaboration.
