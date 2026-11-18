# Shared real/random local architecture for mddhAdv_le

Scratch only; not native checked. The full declaration is in
`MddhAdvLe.refactored.lean.inc`; the same outer proof body alone is in
`MddhAdvLe.refactored.proof.lean.inc`. No new public statement, helper, algorithm,
sampler or machine is introduced. The frozen docstring and theorem header are unchanged.

The live theorem was read from the managed worktree on this invocation. The four completed
segments hEnds, hPreScalar, hLossBudget and hCoinUnwrap are copied byte-for-byte from that
source, including root's repaired global dotProduct names and reduced Fin constructors.
A Python exact string comparison checked all four copies and the docstring/header. No Lean,
lake, build, Git command or live edit was performed.

## Architecture and exact remaining admissions

The former two close holes are replaced by one common parent-scope observer and tape layout:

- SType/UType are the exact untouched scalar matrix types over pp.group.order.
- obs averages the original D.Coins on the actual encoded group challenge. Its selected
  column is supplied explicitly; earlier columns use M*S, later columns U. Both whole
  selected columns of S and U are ignored by obs itself.
- idealCore(real=true) has a uniform base M and real selected response M*rs.
  idealCore(real=false) has a uniform base M and independent uniform selected column v.
- plantedCore always draws ab, rs, t and L, and uses the exact scalar selected column
  L*[ab0*rs0,ab1*rs1,if real then rs0+rs1 else t]. Thus one hPreScalar call layout works
  in the remaining generic transport proof, without branching or changing the actual draw.
- ideal and planted average these cores over S and U; coreLoss is the exact Bool-indexed
  canonical bound. hCorePoint dispatches only the already-proved ColumnLaws. Its real
  branch reuses dlinMatrix_mulVec for the real-vector identity and expect_const for the
  independent original t sample. One hClose averages over U, S and pp. The old close
  statements are term specializations, preserving every downstream verified proof.

Exactly TWO named term-sorry obligations remain, both quantified ∀κ j real:

1. hReductionTransport: avgTape of actual redGame equals pp-average of planted. Fill using
   actual public DLIN/preprocessor readers, hPreScalar, order transport by ringEquivCongr,
   uniform sample-equivalence and pair/Fubini/commutation laws. Every original tape entry,
   unused coordinate, scalar draw and D coin stays represented. This obligation is now
   shared across both real/random branches, rather than duplicated.
2. hHybridResample: the actual adjacent hybrid (j+1 for real, j for random) equals pp-average
   of ideal. Transpose S into whole columns and use expect_sample_coord with β=Fin2→K in
   the real case; transpose U with β=Finℓ→K in the random case. The chosen column is ignored
   in the residual observer, so the existing generic resampling law applies. No counting
   proof should be copied or new host/helper introduced.

## Searches and exact reuse

This invocation read the full live mddhAdv_le and both canonical ColumnLaw headers/bodies.
Static queries:

- `rg -n '^theorem dlin_(real|random)_column_gap_le|^theorem mddhAdv_le|^end BilinearGen'`
  in ColumnLaws and SelfReduction; sed ranges295-730 and237-302 respectively.
- `rg -n 'mulVec.*(apply|sum|cons)|mulVec_cons|mulVec_eq|dotProduct.*cons|dotProduct_cons|vecMul_cons'`
  over Mathlib matrix sources; one guessed Data/Matrix/Notation path did not exist.
- `rg -n 'eta.*(two|2)|forall_fin_two|vec2_dotProduct|cons_mulVec'` over Mathlib
  Data/Matrix, LinearAlgebra/Matrix and Data/Fin. Nearest exact finite-vector readers are
  Matrix.cons_mulVec and Matrix.vec2_dotProduct; the existing dlinMatrix_mulVec already
  packages the full required identity, so it is consumed instead of a new arithmetic proof.
- Read Pairing/Linear:108-143, which supplies dlinMatrix_eq and dlinMatrix_mulVec.
- Read ColumnLaws:227 onward for exact random ab/rs/t/L draw order. It matches plantedCore.
- Existing earlier searches in MddhAdvLeHRealClose-NOTES record Probability's generic
  expectation, sample equivalence/Fubini and coordinate-resampling APIs, including their
  exact shapes. They are unchanged by this refactor.

No new generic algebra fact is proved. hVector is just an application of the existing
public dlinMatrix_mulVec theorem, with Fin.forall_fin_two providing the two-coordinate
word extensionality. Only proof-local definitions appear in dsimp lists. Foreign public
algorithms and ProbComp.prob are read through their published equations, not unfolded.

## Check boundaries / possible elaboration repairs

This is one newly authored outer tactic block architecture. The four existing local `by`
proof bodies are copied verbatim, not new proof invocations; newly filled substeps use the
existing sorry-ladder `?_` / swap discipline. The two explicit prime/NeZero instances before
ColumnLaw calls are retained to avoid the previous synthetic Field(ZMod _) diagnosis.

The intended definitional reductions in hCorePoint concern ONLY the proof-local definitions
A0/idealCore/plantedCore/coreLoss and canonical Bool cases. No foreign public algorithm is
used by defeq. hPlantedReal simplifies the closed real-bit conditional and uses the local
hVector equality plus published expect_const. Native checking remains root's next step;
no successful seal/typecheck or standard-only chain is claimed.

The real-only81-line draft is retained as superseded evidence; it is not the insertion plan.
The original live full file has 697 lines; inserting this refactor would have
821 lines before filling the two shared hard equalities. If those fills approach1000,
extract proof-only scalar transport into a cycle-free theorem module using the same public
readers; do not duplicate independent averaging/resampling proofs.
