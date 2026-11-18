# Classes and layered partial-garbling drafts

These are unelaborated M0 drafts, not checked source or a checkpoint. No Lean,
lake, build command, Git command/mutation, further agent, sampler, or efficient
partial-garbling instance was created. Both files use term proof bodies and no
`by` tactic block. The lead owns checking and promotion into the worktree.

- `Classes.lean`: 490 lines, maximum width 97, nine substantive admissions.
- `PartialGarbling/Layered.lean`: 457 lines, maximum width 95, nine admissions.
- `classes-layered-declarations.tsv`: 126 source declarations, full names/lines.
- `classes-layered-admissions.tsv`: all 18 current admitted bodies.
- `classes-layered-searches.log`: local name/conclusion-shape searches and reused APIs.
- `classes-layered-static-checks.txt`: widths/counts/hashes; explicitly not Lean results.

## Approved refinements

1. `PolyTensor p l n d` is a shared typed coefficient tensor. Class descriptions
   flatten its output/tuple axes through `finProdFinEquiv` and the published
   base-(l+1) `finFunctionFinEquiv`; there is no Fintype.equivFin.
2. Class parameters are positive moduli and class outputs are residues. The
   new parent FnClass.encValue fields use `encodeScalar p`, the published
   singleton modular-vector encoding at Nat.size p. Its injectivity is a direct
   term application of encodeVector_injective and Nat.lt_size_self. This
   preserves µ for the scalar simulator; no target-group encoding is substituted.
3. Public/function/private class words have widths based on the supplied w.
   Their interpretation is total for ALL p, including representatives ≥p.
   Representation COMPLETENESS/encoding round trips require p≤2^w. This is
   disclosed by phfeClass_eval_encoded and the tensor round-trip hypotheses;
   actual group use supplies the reachable modulus/width bound.
4. A total decoder reuses Encoding.Modular.decodeVector at q=2^w and casts
   each resulting integer into p. Every fixed-size word passes that parser.
   The fallback is explicit zero but unreachable, proved by a term guard
   argument. decodeResidues_apply gives literal integer-block reduction mod p,
   not rejection of values outside p. Zero width is supported.
5. The raw PG family has ALL positive moduli and uses tensor description width
   Nat.size p rather than the public class's fixed w. Thus its encFn injection
   remains possible for arbitrary p. Future honest algorithms can re-encode
   their decoded tensor into this canonical PG description; no prime schedule
   is computed or hard-wired.
6. PartialGarbling/Layered imports PartialGarbling/Defs, not the parent facade,
   following the lead's approved pre-M0 split to avoid an import cycle.

## Classes and exact widths

Let l,n,n1,n2,w denote PolyExprs and d a fixed natural degree. At κ:

| Class | public bits | private bits | function bits |
|---|---:|---:|---:|
| phfeClass l n w d | l·w | n·w | ((n·n)·(l+1)^d)·w |
| quadClass l n1 n2 w d | l·w | (n1+n2)·w | ((n1·n2)·(l+1)^d)·w |

The typed tensor evaluates `Σ_tau C_j,tau Π_i xhat(tau_i)` with xhat=(x,1).
The quadratic class evaluates `(z1⊗z2)·f_C(x)` using Matrix.kroneckerMap.
The PHFE class restricts this to z1=z2=y. phfeEval_sum states the precise
`Σ_j,k f_jk(x)y_jy_k` expression. The wire-level embedding keeps coefficient
and public words unchanged and duplicates private residue rows without decoding.
It holds for every word/modulus, independently of the encoding-width bound.

`BidegreeAtMost d 2 P` constrains the sums of public/private variable exponents
of every nonzero coefficient monomial in an MvPolynomial. `pad_one` is the
actual completeness statement: every such polynomial has a tensor C whose
PHFE evaluation at (y,1) equals P(x,y). It is not merely a tautological padding
identity. Its proof is a later coefficient/monomial expansion argument, not an
honest algorithm or an efficiency claim. The representation is an explicitly
restricted polynomial-vector instance of Wee20's ABP class.

## Layered construction

The exact mathematical formulas and boundary calculations were previously
verified in `/private/tmp/io-phfe-source-review/partial-garbling/LAYERED-FORMULAS.md`.
The draft implements those formulas:

- MIdx is the sigma of tuples at depths 0 through d; root is the empty tuple.
- TIdx is the sigma of positive-depth tuples, indexed by predecessor depth.
- Both enumerations use tupleCoord followed by finSigmaFinEquiv, fixing depth
  order and arithmetic base-(l+1) tuple ranks. No new Sigma instance is declared;
  raw fields use existing standard finite/equality instances on these concrete
  types.
- L1 has the variable-labeled parent-to-child incidences. L0 has padded-constant
  incidences, −1 at every non-root diagonal, and terminal coefficient entries.
  Their shapes are exactly t_rng×(l·m) and t_rng×m.
- nodeCount=Σ_{k≤d}(l+1)^k, auxCount=Σ_{k<d}(l+1)^(k+1), auxCount+1=nodeCount.
  Thus t_rng=auxCount+n′=m+n′−1, independent of the tensor coefficient values.
- Reconstruction contains f_C(x), then forward prefix products.
- Backward values are explicit suffix sums; `extend` uses Fin.append with the
  canonical k+(d−k)=d cast. There is no well-founded recursion or witness choice.
- The draw shift has private values in its last n′ entries and backward node
  values elsewhere. The pointwise identity is real(t)=ideal(µ,t−shift).
- Exact privacy reindexes the uniform draw by Equiv.addRight(−shift), using
  ProbComp.expect_sample_equiv. There is no privacy/rank error term.

Every statement allows d=0 and n′=0. At d=0, MIdx is the singleton root,
TIdx is empty, and garbling is `(z−t,Σ_j t_j C_j)`. At n′=0, the allowed value
and backward shift are zero, and real/ideal garblings coincide. If both vanish,
the coin type is a singleton (functions on an empty domain), the garbling has
one zero coordinate, and reconstruction there is 1. No empty-vector positivity
hypothesis has been introduced.

## Sources read and visual verification

The lead and this subagent verified all five source hashes before reading PDFs.
Earlier PG review: complete pages AGW20 11,12,37–39 and IW14 6–11 were rendered
and visually inspected. This task additionally read and inspected complete
GJLS21 PDF pages 61–62 (printed 57–58, §9) and Wee20 PDF/printed page 6 (§3).
Those full-page scratch PNGs and extracted text are under this temporary draft
folder. They are reading intermediates, not proposed delivery contents; promote
only source notes/hash/inspection logs by default, not paper text/page images.
No PDF was copied.

Source readings/deviations to retain in REPORT:

- GJLS21 §9, printed pp.57–58, specifies the quadratic private class and scalar
  values embedded in GT. The library function class keeps scalars for simulator
  leakage; the FE embed supplies the group-valued result.
- Separate l and n are a parameter generalization; GJLS21's equal lengths are
  obtained by l=n. Ordered padded tuples replace monomial/ABP syntax.
- Wee20 §3, p.6, supplies the `(z1⊗z2)f(x)` class. This is restricted to bounded-
  degree polynomial vectors, with the shared tensor evaluator.
- The padding completeness theorem makes explicit the §9 implementability
  observation. It is a derived formal bridge, not a separately numbered source
  theorem or quotation.
- AGW20 Lemma 2's swapped L0/L1 dimensions are corrected by Appendix A (32).
- IW14 Definition 1 supports exact privacy. IW14 Theorem 3 at one private-tail
  column supports the chosen degree-one syntax; the stronger single-coordinate
  “affine” syntax is not claimed.
- Forward/backward path sums replace the source determinant proof. No ABP
  datatype, determinant lemma, or IK02 import appears.

## Overlap and reuse by declaration group

| New declarations | Existing API / nearest relatives |
|---|---|
| PolyTensor, xhat, polyTensorEval and readers | New coefficient representation; xhat reuses Fin.snoc and its readers (Mathlib/Data/Fin/Tuple/Basic.lean:495–519). Finite products/sums remain Mathlib operations. |
| tupleCoord | Direct wrapper of finFunctionFinEquiv, Mathlib/Algebra/BigOperators/Fin.lean:555–586; no alternative ranking. |
| decodeResidues and guard/component readers | decodeVector_eq, Encoding/ModularDecode.lean:59–69; Candidates.listToNat_lt_two_pow, Candidates/Arithmetic.lean:166; List.length_take_le; ZMod.val_cast_of_lt. No copied parser or numeric decoder. |
| residue/tensor round trips and injection | Encoding.Modular vector/matrix round trips and injectivity (ModularDecode.lean:90–235; Modular.lean:101–142); only reindexing/typed-input glue is new. |
| encodeTensor, encodeTensorBits | encodeMatrix and encodeMatrix_length; List.ofFn_get/getElem are nearest reading round trips. The explicit fixed-width bit view adds no new modular encoding algorithm. |
| privateTensor, quadEval, phfeEval | Matrix.kroneckerMap and dotProduct; new source-specific function-class wrappers. |
| encodeScalar / injectivity | Published encodeVector and encodeVector_injective at Fin 1, with Nat.lt_size_self. No scalar encoding re-proof. |
| phfeClass/quadClass and projection readers | Parent FnClass interface; new class instances with source-specific evaluations. |
| duplicatePrivateBits / class embedding | finProdFinEquiv, finSumFinEquiv and their published application/inverse readers. No custom finite-product bijection. |
| BidegreeAtMost/pad_one | MvPolynomial.coeff/eval and polynomial finite coefficient expansion; nearest Mathlib totalDegree bounds are global, while this statement needs separate variable-block sums. |
| Layered MIdx/TIdx/root/node/parent/lastLabel/leaf | Explicit prefix representation; parent uses Fin.init, leaf/source use standard Fin constructors. No ABP model or new generic tree datatype. |
| counts and explicit coordinates | Fin.sum_univ_succ; Equiv.sigmaCongrRight; finSigmaFinEquiv/:apply at Mathlib/Algebra/BigOperators/Fin.lean:656–668. No cardinality-based opaque equivalence. |
| L0/L1/matrix and readers | New source-specific incidence matrices; publicTensor and Mathlib matrix operations are reused. |
| forward/rec | Fin.prod_univ_castSucc and the empty-product API specialize to this representation. No independent generic product theorem. |
| extend/backward/shift | Fin.append, Fin.consEquiv/Fin.snoc, Nat.add_sub_of_le; new source-specific path formulas. |
| forward_action/backward_action/backward_root/rec_spec/translation | New layered PG identities; use existing matrix linearity, dot-product/mulVec, finite-sum reindexing APIs rather than restating them. |
| exact privacy | ProbComp.expect_sample_equiv, Games/Probability.lean:304–306, with Equiv.addRight. No second probability reindexing theorem. |
| layeredPG_raw and projection readers | Raw family assembly only; the efficient interface is not inhabited here. Standard finite/equality instances are projected into raw fields, not redeclared for Sigma types. |

No exact?/apply? or elaboration result is claimed; those checks remain for the
lead's authorized route. In particular the lead should check term inference in
decodeResidues_parse/apply, inherited FnClass scalar-encoding fields, and the
concrete finite-coordinate construction fields before promoting this draft.
