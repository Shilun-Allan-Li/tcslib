# Gate 48 · round 2 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate48-bb1-sim-r2-findings.md`).

---

**CLEAR — 0 blockers, 0 majors, 1 minor, 0 notes.**

Audited [PR #357](https://github.com/Shilun-Allan-Li/tcslib/pull/357), Gate 48, round 2.

| Pin | Commit |
|---|---|
| Lean head | `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d` |
| Campaign records | `3bc01cd7201bc4fd1c3f5cf43c653bc0a7198e23` |
| Exchange | `4f436b659e3cb0cd633d82cd68cf3d869ed6a449` |

**G48-01: closed.** The new head's sole parent is round 1's `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`. Its complete diff is exactly **one file, +1/−3**, inside `bb1_sim_real`: delete local `h01` and apply `abs_sub_le_of_nonneg_of_le` to the same four probability bounds, in the same order. The committed diff equals the supplied diff byte for byte. Everything outside that proof edit is unchanged; the Mathlib application establishes the same bound.

| New finding | Severity | Evidence | Proposed fix |
|---|---|---|---|
| **G48-02** | **minor** | At the records pin, `briefs/pairings/gates/48-bb1-sim-fill/pack-r2.md` and `dispatch-r2.md` still describe the abandoned debt-only round: unchanged head `7a98ba01`, exchange `5976f1a0`, and Stage-2 repayment. The records-side `records-r1-r2.diff.txt` also retains that older delta. Moreover, `SHA256SUMS-r2:2` expects `ff123aa9…` for `resolutions-r1.md`, whose revised contents hash to `06695f97…`; only 4/5 entries verify. These documents lack a superseded label. | Refresh the records-side pack, dispatch and delta to the LE-g48 round, or explicitly archive and label the old versions. Regenerate the corresponding checksum list. |

The dispatched exchange pack and LE-g48 evidence verify. G48-02 is a records documentation defect and does not prevent CLEAR under the stated gate rule.

| Check | Result |
|---|---|
| Integrity | **9/9** exchange-folder checksums and **102/102** evidence-archive checksums pass. The exchange's records delta exactly matches the four actual records files between the pinned commits. |
| Replay binding | All **4/4** build sources bind to `dfdc56f2`; recorded rc, errors, warnings and `sorry` counts are zero, with empty hashed build logs. Independently reproduced the four-module reverse import closure and the **4 build / 1428 reuse** plan. |
| State and snapshots | Input state equals round 1's output state. Independently recomputed all **1432** old and new import-closure keys; all state checks agree. Records show both protected trees rehash **0/0/0** before, after building and after checks, and all four rebuilt oleans have link count 1. The **1463**-entry output map matches state; only `BonehBoyenSecurity`'s olean differs from round 1. |
| Admissions and axioms | Per-module admissions are unchanged, total **192**. The identical axiom probe reports **76** standard constants, six empty traces and the expected failing sorry control. Its raw log differs from round 1's only in the two disclosed closure sizes; `bb1_sidSecure` has an empty trace over **20,374** constants. |
| Rule 10 | Independently reconstructed the omitted coe-A probe **and JSON**, matching both recorded hashes exactly. All **2319** request rows and term metadata equal round 1's. The run records report zero errors; collector and seal log digests equal round 1's. |
| Carry-over | Justified for the other 35 seals, controls and unfold scan: imports, declarations, readers and definitions are unchanged; the replacement invokes a Mathlib theorem and introduces no explicit unfolding. Round-1 passes were carried forward. |
| Lint | Fresh campaign lint exactly reproduces the supplied output: **92 FAIL / 104 WARN** over 529 files, with non-INFO output unchanged from round 1. Fresh file style lint: **0 findings**. |
| Substantive records | DL-58 is marked repaid, its Stage-2 line is struck, and the review contains the dated correction and LE-g48 update. The live PR head and description match the current exchange description. |

No other new undisclosed change was found. I did **not** execute Lean afresh: build, snapshot and dynamic-check outcomes above are verified execution records. Four artifacts were explicitly omitted from the archive; the seal source and JSON were recovered by exact hash reconstruction, while the raw collector/seal logs remain on the maintainer host. The specified out-of-scope items were not re-audited.
