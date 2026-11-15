# sc-garble · ruling SG-1: frozen-file exception (Seyoon, 2026-11-15)

Seyoon ruled this before dispatch, and it is part of the issued package. Where it differs from
[the brief](brief.md), the ruling takes precedence. It replaces the last two sentences of the third bullet of *The import
direction*: "which you may not make public or delete" and the ledger-row disclosure. Everything else in the brief
stands.

## The question
`specialScheme_multiMessageSecure` cannot be proved through `specialScheme_multiMessageSecure_of_joint`, because
`SpecialEncryptionMulti.lean` imports `SpecialEncryptionSecurity.lean`. The brief therefore proves it directly from
D4. That proof needs public coin-relabelling readers of `specialScheme` in `SpecialEncryptionSecurity.lean`, and
those readers repeat six frozen private helpers of `SpecialEncryptionMulti.lean`.

## The ruling: remove the private copies in this unit
Publish the relabelling **once**, as public readers beside `specialScheme` in `SpecialEncryptionSecurity.lean`, as
the brief says. Then, in `SpecialEncryptionMulti.lean`, you **may**:

1. **Delete** exactly these six private declarations:
   - `specialScheme_gen_runAt`
   - `specialScheme_enc_runAt`
   - `specialKeyEq`
   - `ofFn_specialKeyEq`
   - `specialNonceEq`
   - `ofFn_specialNonceEq`
2. **Re-prove `specialScheme_multiMessageSecure_of_joint`, proof only,** through the new public readers. Its header
   stays byte-identical. Its docstring, including the statement prose and the `**Proof sketch.**`, stays
   byte-identical unless the sketch names one of the deleted helpers. In that case, change only that name.
3. Make **no other change** to `SpecialEncryptionMulti.lean` beyond what the brief already allows: the proof of
   `sliceMultiMessageSecure_of_prfOut` and its sketch, the module docstring, and imports of its helpers. In
   particular, `zipWith_xor_append_of_le` and every other private declaration stay.

With the private copies gone, the overlap is not debt. Disclose the replacement in `REPORT.md` § *Overlap and reuse*:
which readers replace which private helpers, and the diff of `specialScheme_multiMessageSecure_of_joint`'s proof.
No ledger row is opened.

## Names
The new public names no longer have to avoid the six deleted names. They must still pass the name-clash scan
against everything else upstream and downstream, including `zipWith_xor_append_of_le` (the DL-46 clash class). Use
names that say what they relabel, under the `SecureComputation` namespace. Each name gets a formula docstring.

## Checks this changes
- **Header check** (*The frozen-statement rule*). The expected report for `SpecialEncryptionMulti.lean` is
  **exactly six REMOVED** (the names above) and **zero CHANGED**. Every other base declaration is present, in the
  same order, with its header byte-identical, and every definition body is byte-identical. Make the checker list
  these six as expected removals, so that anything else is still a difference. Keep the one-character control, and
  add a second control: deleting a seventh private declaration in a copy must report exactly one unexpected
  removal.
- **Proof changes outside the targets.** `specialScheme_multiMessageSecure_of_joint` is the only non-target
  declaration whose proof may change. Report its old and new proofs side by side under `evidence/headers/`.
- **Downstream.** The six helpers are private, so no other file can use them. Show this with a search over the
  project and `audits/`, and file it under `evidence/headers/`.
- **Rule 10.** Seal `specialScheme_multiMessageSecure_of_joint` with the new readers, in variants A and B, strict and
  coe, as for the targets.

Every other change to a frozen file still needs a scope request.
