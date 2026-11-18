# paddedIncidence_eq proof candidate

Exactly one existing theorem proof is supplied. The live header, including the explicit
constant family `Fin.snoc (α := fun _ => R) x (1 : R)`, is unchanged. The current full
docstring and proof sketch are retained. The fragment has 42 lines, maximum width 90,
one tactic block, no admission, and no new public helper. No live edit, Lean/lake
invocation, Git command, proof checker or new agent was used. The lead must validate it.

## Required searches already performed by the lead

The lead ran exact?/apply? against the corrected, well-typed header. The raw logs are:

- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_PathAlgebraReuse2.log;
- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_PathAlgebraApply2.log.

The exact? run reports no complete proof for the padded formula. The apply? run offers
only partial suggestions. The earlier typing failure is not present in the run2 exact?
log. The agent's focused name/conclusion and public-lemma searches are saved separately
in `paddedIncidence_eq.searches.txt`. The current TCSlib name hit is the live header
created by the lead, not a prior public proof.

## Exact reuse

- Matrix entry equations: `Matrix.add_apply` (LinearAlgebra/Matrix/Defs:216),
  `Matrix.of_apply` (:83), and `Matrix.mul_apply` (Data/Matrix/Mul:293).
- Product-index sum: `Fintype.sum_prod_type`, generated in
  Data/Fintype/BigOperators:251-256. It splits Fin l × V directly; no local product-sum
  induction or copied reindexing theorem is introduced.
- Supported node sum: `Fintype.sum_ite_eq'`, generated at
  Algebra/BigOperators/Group/Finset/Piecewise:292-295. The coefficient is first put into
  nested conditional form using `ite_and` (Logic/Basic:910) and `ite_mul`
  (Algebra/Notation/Defs:116), then the published singleton sum evaluates at parent e.
- Supported variable-label sum: `Fintype.sum_ite_eq`, generated at Piecewise:287-290,
  after `Fin.castSucc_inj` (core Init/Data/Fin/Lemmas:571) removes the embedding.
- Padded-label cases: `Fin.lastCases`, core Init/Data/Fin/Lemmas:985;
  `Fin.castSucc_ne_last`, Data/Fin/SuccPred:196; `Fin.snoc_castSucc` and `Fin.snoc_last`,
  Data/Fin/Tuple/Basic:506 and :519.
- The local hlast is only `Ne.symm (Fin.castSucc_ne_last i)` to orient the already
  published disequality for the constant-label branch. It does not introduce another
  finite-index fact or prove a generic lemma.
- Empty/zero expressions use existing `Finset.sum_const_zero`, `one_mul`, `zero_mul`,
  `mul_one`, `mul_zero`, `zero_add`, `ite_self`, and `sub_eq_add_neg`.

All simp entries are public lemmas or hypotheses, never foreign definitions. No TCSlib
definition or admission is read. No finite-sum, block-matrix, tuple or single-coordinate
law is reproved. This proof does not depend on either of the other two new PathAlgebra
helpers. The current imports already provide the used lemmas: Tuple.Basic imports
Fin.Rev, which imports Fin.SuccPred. No additional Mathlib root is needed.

The proof preserves multiplication order and is valid over an arbitrary ring, including
noncommutative and trivial rings. It handles l=0 through the constant branch of
Fin.lastCases and requires no injectivity/distinctness of endpoints or positive-size
hypothesis. No mathematical obstruction was found.
