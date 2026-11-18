# Degree proof candidates and PolyTerms reuse notes

Prepared read-only before M1 proof work. No source file was edited. No Lean, Lake,
build, cache, exact?, apply?, axiom, or seal command was invoked. Each `.proof` file
is one replacement body for the correspondingly named existing theorem in Degree.
They are unelaborated candidates, not checked proofs. Each tool invocation wrote at
most one tactic block; the first six candidates are tactic-free terms.

Apply/check `Degree/01` through `06` first, inside namespace Internal. They use only
public preexisting Mathlib facts. `07`/`08` use Mathlib directly. `09` through `22`
reuse the six upstream helpers after those helpers are actually proved. No candidate
uses a downstream theorem, its own theorem statement, or a private stand-in as a
fact. `23`/`24` use the existing public weighted rename theorem directly and owner
`pubDegree_eq`/`privDegree_eq` readers. The specialized candidates do not unfold a
foreign TCSlib definition.

The two input source files were unchanged by this task. Degree has 24 named holes;
PolyTerms has zero holes and all five definition/abbreviation readers are already
`rfl`. There is therefore no PolyTerms M1 proof body to fill in this snapshot.
Do not add new PolyTerms helper statements merely to produce proof work.

## Precise public reuse

Paths below are inside the pinned `.lake/packages/mathlib/Mathlib/` source tree.

| Existing public lemma | Location | Candidate using it |
| --- | --- | --- |
| `AddMonoidAlgebra.sup_support_add_le` | `Algebra/MonoidAlgebra/Degree.lean:85` | 01: weighted degree is definitionally support.sup of the weight map. |
| `AddMonoidAlgebra.sup_support_mul_le` | `Algebra/MonoidAlgebra/Degree.lean:100` | 02: weight is an AddMonoidHom, so map_add supplies the required inequality. |
| `AddMonoidAlgebra.supDegree_sum_le` | `Algebra/MonoidAlgebra/Degree.lean:241` | 03: compose the sup-of-degrees bound with `Finset.sup_le h`; no induction. |
| `AddMonoidAlgebra.supDegree_prod_le` | `Algebra/MonoidAlgebra/Degree.lean:290` | 04: map_zero and map_add of `Finsupp.weight w`; no induction. |
| `AddMonoidAlgebra.sup_support_finset_prod_le` | `Algebra/MonoidAlgebra/Degree.lean:181` | Existing alternative generic API found; not separately rederived. |
| `MvPolynomial.isWeightedHomogeneous_C` | `RingTheory/MvPolynomial/WeightedHomogeneous.lean:198` | 05: constants are homogeneous of weighted degree zero. |
| `MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero` | `RingTheory/MvPolynomial/WeightedHomogeneous.lean:543` | 05: directly converts the constant homogeneity fact to degree zero. |
| `MvPolynomial.isWeightedHomogeneous_X` | `RingTheory/MvPolynomial/WeightedHomogeneous.lean:214` | 06: every supported monomial has weight w(i); sup <=w(i), even in a zero ring. |
| `MvPolynomial.mem_support_iff` | `Algebra/MvPolynomial/Basic.lean:543` | 06: turns supported monomial into nonzero coefficient for the homogeneity fact. |
| `MvPolynomial.weightedTotalDegree_zero` | `RingTheory/MvPolynomial/WeightedHomogeneous.lean:108` | 07/08. |
| `MvPolynomial.weightedTotalDegree_rename_of_injective` | `RingTheory/MvPolynomial/Homogeneous.lean:56` | 23/24, with explicit equality of transported indicator weights. |
| `Sum.map_injective` | `Data/Sum/Basic.lean:250` | 23/24, supplied equivalence injectivity in each summand. |
| `Finsupp.weight` | `Data/Finsupp/Weight.lean:74` | Existing AddMonoidHom, so use generic map_zero/map_add rather than reprove a Finsupp sum-add formula. |
| `Finset.sup_le` / `sup_le_iff` | `Data/Finset/Lattice/Fold.lean:92-97` | 03/06; public order bound. |

The source sketches' support proofs and finite-set inductions for the six weighted
closure helpers should be implemented as these direct public API applications.
The weighted wrappers themselves are still new domain-facing interfaces; the
mathematical support/induction facts already exist generically and must not be
reproved inline. No new Mathlib direct import is proposed: the generic degree API
is already used by the imported `MvPolynomial.Degrees`; the weighted/homogeneous
API is imported by `MvPolynomial.Homogeneous`. Root must confirm elaboration and
any transitively available Sum lemma under the pinned imports.

The initial name/shape search encountered current StructuredSeed targets while
inventorying existing headers. Those self/unsolved matches were not used as search
facts or proof evidence. The recorded `reuse-searches.json` searches for candidate
facts exclude the new Obfuscation area or use explicit public Mathlib files.
`exact?`/`apply?` probes are pending lead-only work, not inferred from these text
searches.

## Candidate risks to resolve in the lead's first checks

The six term candidates rely on the definitional identification of MvPolynomial
with AddMonoidAlgebra and its weighted degree with support.sup. The explicit `show`
terms expose those Mathlib types without passing Mathlib definitions to simp/rw.
If elaboration needs more explicit implicit parameters, add type arguments rather
than unfold a foreign definition or cite the existing sorried target.
The constant candidate relies on the public zero-homogeneity equivalence; the
variable bound intentionally does not use support_X, which would require a
nontrivial coefficient ring. Rename candidates reduce the indicator equality by
cases in a term proof and only rewrite named readers/theorems.

## PolyTerms

No holes exist. The actual encoding reuses `BoolCircuit.encodeList` with
`encodeList_nil` (`Uniform.lean:96`) and `encodeList_cons` (`:100`), and the public
`Turing.pairEncode` / `pairEncode_eq` (`Encoding.lean:139`/`:144`). Public
`pairDecode_pairEncode` (`:160`) and `pairEncode_injective` (`:173`) are available
for future required composition glue, so do not implement another pair decoder.
The BoolCircuit generic prefix-free and upper length helpers at Uniform.lean:158
and :234 are private and cannot be cited as public API. Lamport's public
`encodeList_injective` refers to the distinct nested-pair PrivateKeyScheme encoding,
so it is not a theorem for the chosen BoolCircuit code. No conversion or alternate
encoding was introduced. A future need for public code-composition glue must be
scoped, searched, and disclosed separately; T2's existing denotation target does
not require adding an injectivity theorem now.
