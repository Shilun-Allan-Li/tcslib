# Isolated exact?/apply? overlap probe templates — NOT RUN

This packet contains 29 GOAL templates and a materializer that writes ONE scratch
file at a time. No Lean tactic, elaboration, build, cache, implementation edit, git
mutation, or agent spawn was performed. No tactic block has yet been inserted in
the templates. Root must run each search after M0's queue using its authorized
single-slot runner. The templates themselves are deliberately not Lean source until
their one body placeholder is replaced. Python syntax was checked with compile(),
without pycache; the materializer was not executed to generate/run a Lean probe.

Snapshot `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`. Source bindings in static-checks.json record the M0 statements
read to choose the independent goals. These M0 files are NOT imports of any probe.

## Why self-tautologies are excluded

Importing Degree, Buckets, SparseFactor, Load, Security, Targets, or a topic facade
would put the already-sorried result itself in exact?/apply?'s environment. Renaming
the scratch theorem, clearing local hypotheses, disabling simp, or making a new
namespace does not remove that GLOBAL constant. A direct successful match there
would be circular evidence for overlap.

Instead every template imports only precise EXISTING Mathlib/library roots and the
pinned toolchain's Lean.Elab.Tactic.LibrarySearch. import-exclusion-audit.json follows
the actual comment-aware import graph of all 15 library roots: EVERY one of the 29
resolved environments excludes ALL StructuredSeed modules, not merely its own owner.
The small cryptographic probes import only OneWayFunctions.Basic (five existing
TCSlib modules transitively), never TCSlib.lean or a cryptography facade. Toolchain
modules cannot import project modules. These facts, rather than a name blacklist
or simp setting, exclude every new M0 helper constant from search.

Each generated file contains ONE anonymous example and no preceding helper theorem,
axiom, definition, or proof of its goal. Independent hypotheses describe actual
mathematical input facts: weighted-degree bounds of summands, list coverage/Nodup,
slot uniqueness, or arithmetic positivity. None simply assumes its target. Siblings
are not imported, so running several probes cannot introduce earlier probe results.
Use a fresh scratch-file environment, not an IDE session/import context that already
imports a StructuredSeed owner. Compiled M0 oleans on disk are harmless if unimported;
library search indexes declarations in the loaded environment, not every disk file.

## Mathematical goal design

- Degrees use MvPolynomial.weightedTotalDegree directly for arbitrary Nat weights.
  Public/private renaming probes contain literal Sum indicator weights, no pubDegree
  or privDegree wrapper. Existing zero/rename theorems are separate positive controls.
- Bucket ranks are the literal Finset.univ.filter cardinalities. Optional grid goals
  abstract the already-known rank bound/overfull proposition while retaining the
  dependent Fin product branch. Correction sums use arbitrary optional positions and
  independent uniqueness/support hypotheses. No rank/indexMap/bucketMatrix constant
  remains in any goal.
- Sparse reconstruction replaces row-major sparseEntries by an arbitrary Nodup list
  that enumerates exactly the nonzero positions and fits in t slots. The two matrix
  factors are explicit match/getElem? functions. A pointwise sum version avoids
  counting a suggestion of Matrix.ext alone as substantive reconstruction reuse.
  Separate raw row-major list goals test the actual enumeration mathematics.
- Load goals expand the bucket filter and use existing uprob directly. The binomial
  goal has its exact original arithmetic statement, but Load itself is not imported.
  A fixed-witness probability goal isolates the independent coordinate calculation.

No template weakens or changes an implementation statement. Abstracted goals are
scratch mathematical comparison goals only. A reusable generic theorem proving one
of them is evidence for the corresponding proof route; a failed stronger abstract
probe does not establish that no more specialized public counterpart exists.

## Minimal source imports and known public candidates

Degree closure probes use WeightedHomogeneous plus MonoidAlgebra.Degree; rename uses
Homogeneous, the precise owner of weightedTotalDegree_rename_of_injective (:56).
AddMonoidAlgebra.supDegree_add_le/mul_le/prod_le (Degree.lean:228,285,291) are relevant
existing generic support-degree APIs. Mathlib weightedTotalDegree_zero (:108) is a
positive control. No new generic degree proof is proposed by these probes.

Bucket probes use Finset.Card, Fintype.Basic, Equiv.Fin.Basic; correction-sum probes
add only Fintype.BigOperators and Matrix.Basic. Relevant public names include
Finset.card_lt_card (:296), card_image_le (:214), card_le_card_of_injOn (:411), and
Finset.sum_eq_single. Exact?/apply? may return such lemmas with real remaining
premises; retain those premises for review.

Sparse probes use the existing SparseFactor owner's three Mathlib roots. Public
List.nodup_flatMap/Nodup.filter, mem_finRange/nodup_finRange and getElem/count APIs
are relevant. The OPTIONAL P2 basis control imports only Mathlib.Data.Matrix.Basis,
where Matrix.matrix_eq_sum_single (:111) exists. It is an alternative library
comparison root, NOT a proposal to add an import after the M0 header freeze.
It tests a weaker generic matrix decomposition, not the exact chosen factors.

Load probability probes use OneWayFunctions.Basic and Finset.Powerset. Public
uprob_pi_forall (:118), uprob_eq_one_div_card (:144), uprob_exists_le (:137),
uprob_comp_equiv (:165), and uprob_fst (:175) are the intended component APIs.
The binomial probes import Choose.Bounds and Complex.Exponential; choose_le_pow_div
(:30), pow_div_factorial_le_exp (:250), exp_nat_mul (:225) are directly relevant.
Controls distinguish those established components from the combined new target.

## One-block materialization and interpreting searches

For one example, in one root tool invocation, materialize exactly one selected mode:

    python3 /private/tmp/io-sprg-proof-notes/OverlapProbes/materialize.py degree_add \
      --tactic 'exact?' --output /private/tmp/io-sprg-probes/degree_add_exact.lean

The command writes one scratch file under /private/tmp and does NOT execute Lean.
Its one body consists of classical and the requested search tactic in a single
block. For the independent second mode, use --tactic 'apply?' and a different
output name in a later invocation. The script accepts only those two tactics,
refuses a non-temp destination, and inserts exactly one block. Do not batch a
new block for several probes into one agent/tool invocation. Root alone runs
Lean through its required host wrapper and records the exact command/log/status.
No fallback sorry/admit, all_goals closure, exact self theorem, or proof from a
previous sibling example is generated.

Run P0 full goals first (14). P1 contains controls, alternate expanded subgoals,
and specific rename/consequence goals (14). The sole P2 matrix basis control is
optional. Each template's priority and role is in probe-index.json and below.

A successful exact? search is a closed proof suggestion in that loaded environment;
record the FULL suggested public declaration/proof, not just rc=0. A successful
apply? may intentionally leave goals: capture every residual goal. Lean's pinned
LibrarySearch implementation uses requireClose=true for exact? and false for
apply? (Lean/Elab/Tactic/LibrarySearch.lean:26-68). An Eq.symm/Matrix.ext/transitivity
suggestion that merely restates or decomposes the original problem is not by itself
a reusable proof of the helper; report it as partial, with the remaining obligation.
A definitional/reflexivity solution of a control is valid but is not evidence of a
new named overlap. A failed search means only no result was found under these
imports/search limits; it is not an exhaustive no-counterpart theorem.

The generated examples may fail to elaborate: these templates are themselves
untested. Separate harness/type/import errors from a genuine no-match result.
Do not turn an elaboration failure into evidence of absence. No output/probe result
or axiom check is claimed in this packet. Root's later evidence should distinguish
closed named reuse, closed definitional proof, partial application, no match, and
invalid/harness result. Inspect the selected library proof dependencies as required
before using it in a delivered proof.

## Probe map

| Probe | Priority | Goal/focus |
| --- | --- | --- |
| degree_add | P0 | Internal.weightedTotalDegree_add_le with original mathematical primitive |
| degree_mul | P0 | Internal.weightedTotalDegree_mul_le; generic public support/degree theorem search |
| degree_sum | P0 | Weighted finite sum closure; no hypothesis is the target itself |
| degree_prod | P0 | Weighted finite product closure |
| degree_C | P0 | Constant weighted degree; zero semiring retained |
| degree_X | P0 | Variable weighted degree bound; zero semiring retained |
| degree_zero_control | P1 | Existing Mathlib weightedTotalDegree_zero control |
| degree_rename_control | P1 | Existing weightedTotalDegree_rename_of_injective; proves public counterpart available |
| degree_public_rename | P1 | pubDegree_rename with both wrapper definitions replaced by literal weights |
| degree_private_rename | P1 | privDegree_rename with both wrapper definitions replaced by literal weights |
| bucket_rank_lt | P0 | rank_lt_load with rank/load/bucket fully expanded |
| bucket_rank_injective | P0 | eq_of_rank_eq with only raw finite-filter cardinalities |
| bucket_option_some | P1 | Abstract good branch of indexMap; rank bound premise is independent of option equality |
| bucket_option_none | P1 | Abstract overfull branch of indexMap, preserving dependent Fin witness |
| bucket_single_correction | P1 | bucketMatrix_apply_indexMap abstracted to arbitrary optional positions, with independent uniqueness premise |
| bucket_nonzero_support | P0 | bucketMatrix_nonzero_card_le with bucket/matrix expanded and arbitrary positions |
| sparse_rowmajor_nodup | P0 | sparseEntries_nodup with no sparseEntries constant |
| sparse_rowmajor_mem | P1 | mem_sparseEntries_iff fully expanded |
| sparse_reconstruct | P0 | sparseFactor_mul generalized from row-major list to any duplicate-free exhaustive nonzero list |
| sparse_reconstruct_entry | P1 | Pointwise expansion of matrix reconstruction; avoids an apply? result consisting only of Matrix.ext |
| sparse_basis_sum_control | P2 | Existing public Matrix.matrix_eq_sum_single; optional precise library comparison root, not proposed owner import |
| load_fixed_subset | P0 | Local fixed-witness probability needed by bucket_tail; no sorried load/helper imported |
| load_tail | P0 | bucket_tail with its bucket definition expanded |
| load_some_tail | P1 | some_bucket_tail expanded to raw events |
| binomial_bound | P0 | Exact existing M0 binomial goal under existing-library imports only |
| binomial_factorial_step | P1 | Reciprocal-factorial intermediate; seek direct existing counterpart before ordered-division application |
| binomial_choose_control | P1 | Existing Nat.choose_le_pow_div control |
| binomial_series_control | P1 | Existing Real.pow_div_factorial_le_exp control |
| uniform_pi_control | P1 | Existing OneWay.uprob_pi_forall control |

reuse-searches.json records 11 exact source searches, including the pinned tactic
implementation. Static metadata reports template placeholders/import exclusion only;
no .lean execution or search result exists yet. SHA256SUMS binds all staged files.
