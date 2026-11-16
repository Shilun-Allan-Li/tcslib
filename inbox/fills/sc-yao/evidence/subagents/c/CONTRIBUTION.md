# Subagent c: length bounds

Assigned worktree: `/Users/seyoonr/.codex/worktrees/sc-yao-c/tcslib-exchange`.
Local branch `fill/sc-yao-c`; no commits. Source: `HybridProof/Lengths.lean`.
Status: ten whole declarations written; Lean verification is pending the lead bootstrap seed.

## Reuse and overlap

- `length_spEncStr_le`: nearest public relative is
  `SpecialEncryption.lean:258`, `length_spEncStr`. That exact equality requires a sufficiently
  long evaluator pad. The new upper bound permits arbitrary evaluator outputs, so it uses
  `spEncStr_eq`, `length_pairEncode` and Mathlib/core list-length readers instead.
- `length_nestedSpecial_enc_le`: nearest unmerged relative is sc-garble, exchange `a73072f1`,
  `GarblingSecurity/NestedBounds.lean:37`, `GarblingCoins.length_nestedInner`. The latter
  proves exact inner length with a canonical PRF pad; the new statement bounds arbitrary
  nested outputs, so it cannot reuse that frozen, unavailable helper.
- `encodeMsgs_eq_encWords`: nearest relative is the local `henc` in `Yao.lean:352`.
  It generalizes that local calculation to a public generic equation, proved from the
  existing nil and cons readers. It avoids copying
  `ZeroKnowledge/CommitmentLemmas.lean:241`, `length_encodeMsgs_le`, whose module is outside
  the issued order; the length estimates reuse `BinArith.length_encWords_le` instead.
- `length_garbledRow_le` specializes the generic nested bound via `garbledRow_eq`.
- `length_garbledTable_le` specializes `Fintype.card_fun` and `Nat.pow_le_pow_right`.
- Both encoded-table bounds reuse `BinArith.length_encWords_le`, the row bound and the
  four-row bound. The encoded-key and encoded-pair bounds are direct applications of
  that same encoded-word-list theorem.
- `length_message_of_parts_le` uses `length_pairEncode` twice and linear arithmetic.
- Bob output length needs no new lemma: reuse `List.length_ofFn` in the consumer.

Search commands and examined unmerged source are in `search.log`. There are no source
admissions, new attributes, frozen-file edits, or direct unfolds. No Lean command has run yet.

## OT input machines

The lead additionally assigned `HybridProof/OTInputs.lean`, namespace
`TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs`.
Its sender machine extracts the two coin bits at the affine offsets; its receiver
machine extracts an input bit at the quotient index. Both have defining readers,
canonical-layout equations and generic polynomial-time proofs, pending Lean checking.

Reused `EncodingMachines.unaryLength_poly` (:117), `unaryPolyOf_poly` (:123),
`unaryAdd_poly` (:81), `unaryMul_poly` (:90), `getBit_poly` (:174),
`divNum_poly` (:653) and `divNum_eq` (:627). No arithmetic or bit-reader utility was
re-derived. The lead's generic CoinRead window is unnecessary for singleton reads
because `getBit_poly` already provides the precise contract. These machines are new
adapters on the generic call-input layout; final identification with Yao call inputs
and finite product indexing is left to the lead's owned theorem body.

Read-only comparison against #318 `ObliviousTransfer/Efficiency.lean` and sc-compose
`ComposeSecurity/{Efficiency,Lengths}.lean` found generic layout projections,
composition machines and protocol-level message bounds, but no counterpart of the
affine coin-bit/quotient input adapters or these concrete garbling length bounds.
No code was copied. Declaration-index search results are in `parallel-search.log`.

## Two-message views

`HybridProof/TwoMoveViews.lean` gives ten generic transcript, view, output and pointwise
real-sampler equations from a two-message Alice-first shape. No new definitions.

Nearest relatives and reuse:
- Transcript equations specialize `Interaction.lean:421` `Protocol.transcriptWith_eq`,
  the execution successor/zero readers and first-mover reader; all are reused.
- Views and encodings specialize `Interaction.lean:470,491` `Protocol.viewV_eq`/`viewP_eq`
  and `View.encode_mk`, which are reused without unfolding.
- Output equations specialize `Interaction.lean:449,458` `Protocol.outV_eq`/`outP_eq`.
  `Yao.lean:547,560` (`yaoMain_outV`/`yaoMain_outP`) give related concrete equations;
  helpers cannot import Yao because the allowed architecture is upstream of it.
- Real-sampler equations reuse `Hybrid.lean` `HybridProtocol.realA_eq`/`realB_eq` and the
  proved generic encoded-view/output equations. They retain generic private inputs
  and generic Bob coins; no OT- or garbling-specific hypotheses are hidden.
- Unmerged #318 `ObliviousTransfer/Shape.lean:192` `exec_five` and :203
  `transcriptWith_isOT` use the same execution readers for a five-message protocol.
  They cannot be imported (unmerged/in flight), and their five-message shape does
  not establish this two-message contract. #318 `ViewA.lean:93` `realA_realCoins`
  similarly computes a concrete OT sampler with a different shape.
- Unmerged sc-compose `ComposeSecurity/Runs.lean:466,536`
  `realA_compose_eq`/`realB_compose_eq` compute samplers for a composed protocol.
  They are related uses of the same public view/output readers, but require the
  composition shape and do not provide two-message equations. No code was copied.

The raw declaration-index comparison is in `views-search.log`. Verification is
still pending the bootstrap seed; no Lean command has run in this worktree.

Additional SY-5 overlap disclosure: sc-garble's delivered `Garbling.lean:584–592`
contains the inline `hcardNat` in `uprob_not_good_le_of_perm`, bounding
`card(A) * (card(A)-1)` by 12 for at most two arguments. The new
`length_garbledTable_le` instead bounds a table's row count by 4. Both specialize
`Fintype.card_fun`/`card_fin`/`card_bool`; this new lemma uses the public
`Nat.pow_le_pow_right` monotonicity result, while the unmerged proof splits the
three argument-count cases. No code was copied, and that inline fact is not an
importable public interface.

## Verified three-helper snapshot

This section supersedes earlier draft-status notes. `Lengths-02`, `OTInputs-02`,
and `TwoMoveViews-01` all passed with zero errors. `Axioms-02` prints all 28
stored constants and their signatures/axioms, and traces every constant closure:
all have sorried=[] and use at most propext, Classical.choice and Quot.sound.
The subtree style lint reports 0 FAIL / 0 WARN. All twelve whole-file Rule10
diagnostic seals pass; all eight paired controls have their expected error
counts (unsealed zero, sealed exactly one). The copied sc-garble conventions,
source manifests, declaration manifests, all raw logs, runner and references are
preserved here. The lead still reruns final merged verification. No source
change was needed after seal diagnosis. Final sizes: Lengths 197, OTInputs 128,
TwoMoveViews 164 lines, each width at most 100 and no source sorry.
