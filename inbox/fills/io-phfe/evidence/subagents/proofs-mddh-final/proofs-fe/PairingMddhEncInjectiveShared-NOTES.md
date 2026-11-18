# Revised BilinearGen.mddhEnc_injective using shared parameter codec

Status: scratch full candidate checked by inspection only; native verification pending.
No Lean/lake/build/Git/live edits/extra agent were run. Frozen main header/prose byte-preserved;
one tactic block, no remaining holes/sorry, no new helper/import/representation change.
PublicParams.encode_injective and BilinearGroup.groupMatrixEnc_injective are both pending
native integration/checking; no standard-only codec chain is claimed.

The first pairEncode_injective separates pp.encode equality from the paired matrix tail.
The shared PublicParams.encode_injective now supplies hPP directly. Eliminate hPP BEFORE
using the matrix-codec theorem, so both source-group matrix types coincide. Pair-inject the
matrix tail; use groupMatrixEnc_injective separately at base dimensions (ell,2) and response
dimensions (ell,d). Constructor reflexivity finishes. No parameter fields, description
witnesses, generator words, scalar representatives, or DLOGs are reconstructed here.

The entire former local description/generator proof is removed from the revised candidate.
Its original file and notes are preserved without edits, with hashes and replacement path in
PairingMddhEncInjective.SUPERSEDED.md. This is a proof-body refactor only; no existing frozen
statement/prose or public algorithm is changed.

## Actual reads/searches this invocation

Read current live MatrixDH/Defs.lean:100-116 for the exact frozen header, mddhEnc_eq and
constructor shape. Read the supplied PublicParamsEncodeInjective.lean.inc and the earlier
manual PairingMddhEncInjective.lean.inc. Ran a narrow theorem-name search over Parameters
and MatrixDH/Defs to reconfirm current source status: shared encode_injective is not live
yet, and groupMatrixEnc_injective remains admitted. Root owns their integration queue.

Existing public APIs reused: mddhEnc_eq; Turing.pairEncode_injective and Prod.mk.inj;
new shared PublicParams.encode_injective with exact supplied implicit G/kappa signature;
pending BilinearGroup.groupMatrixEnc_injective. No new helper or native reuse probe is
needed in this invocation. All explicit simp entries are public readers; constructor/equality
elimination uses no foreign defining-equation reads.

Native focus: ordinary dependent equality elimination after shared parameter injection and
inference of each matrix dimension at the two pending codec calls. Empty dimensions remain
covered by the original statement and codec theorem.
