# PartialGarbling interface draft

Draft path: `/private/tmp/io-phfe-drafts/PartialGarbling.lean`.
This is an unelaborated draft, not a checkpoint or a claim of successful Lean
checking. No Lean, lake, build command, source edit in a worktree, Git mutation,
new subagent, sampler, or machine construction occurred in this subtask.

## Family refinement and uniformity

The proposed pointwise Raw(p,ℓ,n′,Fn) shape is refined to

    Raw (l n : PolyExpr) (Fn : (kappa : ℕ) → ℕ+ → Type).

All typed matrix algorithms, reconstruction, laws, index types and encodings
range over κ and the positive modulus. This lets each efficient-interface field
state ONE existential polynomial-time map BEFORE `∀ κ (p : ℕ+) ...`.
A constant-p efficiency witness would be too weak; none is used here.

The public parameter word contains fixed-width binary numerals of p,l(κ),n(κ),
where each numeral width is Nat.size of that value. `NUPPT.advInput` separately
supplies 1^κ. The function encoding has a declared finite width and injectivity;
recInput additionally includes the modular vector encoding of x. The modulus
is an input. No function of κ computes or hard-wires a prime schedule.

The positive-modulus family is adequate for this deterministic partial-garbling
interface: no field argument uses inversion or primality. In the cryptographic
instance p will be the drawn prime order. This refinement was explicitly
approved by the lead before the draft was written.

## Exact finite-coordinate contract

- MIdx/TIdx are explicit type families with concrete Fintype/DecidableEq fields.
- mCoord : MIdx ≃ Fin mCount and tCoord : TIdx ≃ Fin auxCount are explicit fields;
  no classical equivalence or Fintype.equivFin is chosen by the encoding.
- auxCount+1=mCount enforces t_rng=m+n′−1. The distinguished m0 maps to finite
  coordinate 0, fixing the paper's e1 placement.
- Row coordinates are TIdx ⊕ Fin n′, auxiliary first/output last.
- L1 columns are Fin l × MIdx, public coordinate first.
- Garbling/reconstruction coordinates are Fin n′ ⊕ MIdx, output first.
- Four named instances only project finiteness/equality for the concrete
  S.MIdx/S.TIdx types. There are no blanket Sigma instances or attribute commands.
- Row/column/output coordinate equivalences have complete term equation readers.

## Raw algorithms and efficient interface

pgbCore and pgbStarCore are generic corrected AGW matrix formulas declared
before Raw. Raw's rec_spec/privacy fields refer to those already-defined
functions. Raw.pgb/pgbStar merely apply them to Raw.L1/L0/m0. Thus neither
of the two garblings can be supplied as a cheating field. The raw law readers
are direct projections; no efficiency hypothesis appears in them.

The efficient PartialGarbling structure extends Raw with exactly lgen_eff and
rec_eff. Their conclusions are the CANONICAL derived output encodings, rather
than arbitrary encoded-output fields. Both are deterministic PolyTimeComputable
existentials, not NUPPT realisation conditions. Neither Raw nor the efficient
interface constructs a sampler. There is no value of the efficient interface
outside a future target assembly.

## Source fidelity

The formulas/Raw law clauses are [AGW20, Lemma 2, p.12], corrected using its
own Appendix A (31)–(32), p.38. Exact privacy is [IW14, Definition 1, p.6].
The efficient family requirement also reflects [IW14, Definition 1
continuation, p.7]. No claim is made of IW14's stronger single-coordinate
“affine” syntax, and no determinant or ABP datatype is introduced.

Only definitions and readers are needed in this interface file, so it has
zero substantive admitted theorem bodies. All readers are term `rfl`, or direct
law-field projections. This also respects the latest one-tactic-block guidance:
the draft contains zero tactic blocks. Target props, target iff readers, the
layered raw instance and target assembly belong to the lead's later modules.

## Overlap and reuse

`partial-garbling-searches.log` records name and conclusion-shape searches in
the pinned TCSlib/audits, Lean 4.25.0 source and pinned Mathlib. No existing
partial-garbling interface/formula was found. The nearest public declarations
were read and reused:

| New group | Reused/nearest public declarations |
|---|---|
| publicTensor and reader | Matrix.kroneckerMap / kroneckerMap_apply, Mathlib/LinearAlgebra/Matrix/Kronecker.lean:55–62; Matrix.one_apply, Mathlib/Data/Matrix/Diagonal.lean:202. No independent Kronecker implementation. |
| pgbCore/pgbStarCore and component readers | Mathlib Matrix.vecMul and matrix multiplication; new source-specific formula, no existing PG algorithm. |
| Raw/PartialGarbling | Finite-group interface field pattern nearest Pairing/Group.lean:96–130; exact-privacy laws use existing ProbComp.expect/sample. |
| paramWord | Candidates.natToList, Candidates/Arithmetic.lean:100–104; Nat.size and lt_size_self, Mathlib/Data/Nat/Size.lean:81. No new numeral algorithm or width theorem. |
| finite coordinate equivalences | finSumFinEquiv / finProdFinEquiv, Mathlib/Logic/Equiv/Fin/Basic.lean:219,325. No new sum/product enumeration theorem. |
| encMIdx/encTIdx | Explicit supplied coordinate equivalences and Candidates.natToList; no classical enumeration. |
| encLgen/encRec and readers | Encoding.Modular.encodeMatrix / encodeVector, Encoding/Modular.lean:51–79, with row-major reindexing. No copied modular encoder. |
| lgenInput/recInput and readers | NUPPT.advInput / advInput_eq, Complexity/Randomized/PPT.lean:210–216, and Turing.pairEncode. |
| reconstruct/exactPrivacy | Direct law-field projections in this module; no re-proof of a public theorem. |
| toRaw_* readers | Inherited-field projection glue; no independent construction. |

Per-helper exact?/apply? probes are deferred to the lead's permitted
LeanInfoView route; the subagent must not run Lean. No proof-search success or
elaboration success is claimed. `partial-garbling-declarations.tsv` inventories
the 48 source declarations with their full names and lines; generated structure
constants still need the lead’s StmtDump census.

## Lead verification points

1. Elaborate the bracketed instance fields and named projection instances;
   their pattern is standard, but no Lean checking was authorized here.
2. Check elaboration of inferred Fin dimensions in modular matrix/vector
   encoding lambdas and of inherited `toRaw` references in efficiency fields.
3. All rfl readers were reviewed statically. In particular publicTensor_apply
   reduces only this module's definition and Mathlib definitions, which the
   dispatch permits; no foreign definition is passed to rw/simp/unfold.
4. Pairing-specific group-lifted pgbStar readers can be added once the lead's
   Pairing.Exponents API is available; no discrete log should enter them.
5. Layered.PGTargets must inhabit this uniform family interface, not a weaker
   per-prime efficiency proposition. Its coordinate ordering must match the
   explicit mCoord/tCoord fields.
