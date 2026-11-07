# CCA2Scheme: first coin-length proof repair proposal

**UNAPPLIED; native elaboration and sealed replay pending.** Frozen head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. The completed seal manifest records that same head,
and the current CCA2Scheme bytes match its source fingerprint. No Git, Lean/cache command,
app, or library edit was used in this invocation.

## Diagnostic mapping and causes

The completed probe reports exactly four `rfl` failures. The preamble installed all 1,704
requested seals (1,685 active, 19 already irreducible); the EOF check verified all 1,704.
These are source proof failures, with no reported seal-command error.

| Probe line | Frozen source line | Site | Disposition |
|---|---|---|---|
| 2092 | 320 | `ccaScheme.correct`: local `hρ`, generator coins | **Only repaired proof block in this proposal.** |
| 2094 | 322 | `ccaScheme.correct`: local `hr`, encryptor coins | Unchanged; same interface issue, separate next step. |
| 2104 | 332 | `ccaScheme.enc_length`: local `hρ`, generator coins | Unchanged; same interface issue, separate next step. |
| 2107 | 335 | `ccaScheme.enc_length`: local `hr`, encryptor coins | Unchanged; same interface issue, separate next step. |

The original `simp; rfl` reduces `List.length_ofFn` to a goal about `NUPPT.coinLen`.
Its final `rfl` then reads the foreign ordinary definitions `NUPPT.coinLen`,
`NUPPT.ofPolyTimeUniform` and its underlying constructor to recover the coin polynomial.
All three are installed irreducible in this closure. The mathematical coin counts remain
`3*n` and `n`; the failures do not indicate changed sampler behavior.

The four displayed goals are independent coin-count conversions. In particular the encryptor
count does not follow from the failed generator count; it still fails with `hρ` present in its
context. Repaired-source checks may reveal further issues, so this is not an exhaustive verdict
on the repaired module.

## Proposed change

Replace only the first local `hρ` proof at frozen source line 320. Read the function-domain
length with `List.length_ofFn`, the coin-length definition through `NUPPT.coinLen_eq`, and
the machine's coin polynomial through `NUPPT.coins_ofPolyTimeUniform`. Evaluate the explicit
`3 * var` polynomial through `PolyExpr.eval_mul`, `eval_const`, and `eval_var`.

All six entries in the new `rw` list are public theorems. The local `ccaGen` abbreviation may
expand when matching the public constructor equation; no foreign definition is unfolded by
the proof. No new helper, reading lemma, tactic block, or admission is introduced. Exactly one
existing local tactic block changes. All other proof blocks, public headers, definition/data
fields and admissions are preserved byte-for-byte. The other three diagnostic sites remain
unmodified and are expected to require their own public-reader repairs.

## Fingerprints

| Artifact | SHA-256 |
|---|---|
| Frozen `CCA2Scheme.lean` | `c361af28d05eb36cbbfe91d43c0f9b6856d9abf98e7ed4bfaf2e6cff433cb70b` |
| Proposed `CCA2Scheme.lean` | `508940311f491e5555202920c4e44e6b61a65ffd5eea4ab546620bc41eba5cff` |
| Proposal patch | `ac644eb1ed3d76b21090cc1b3b523c9c1c0c72336b86a7be93e5fc92eb82118e` |
| Public-reader home `PPT.lean` | `1766685ee73e2221d7cdecffe8a8cafedc43dc46af2d1b06da8c750973a453f4` |
| Polynomial-reader home `PolyExpr.lean` | `69b3f23c2eddbaa479c1ea23c3cee9960cc30553bb846be1a4a9d408bae69903` |
| Completed seal log | `1abdabf3b1873802a82990064ad656e183983758355b571cefef57c846327fdc` |
| Completed seal manifest | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs/G06Seal_011_TCSlib_Cryptography_Composability_CCA2Scheme.log`.
Source line mapping: the matching probe record's `source_to_probe_lines` in that manifest.
The proposal has been checked only by source inspection and in-memory patch application;
root must run the changed proof and its full-closure seal after accepting/applying it.
