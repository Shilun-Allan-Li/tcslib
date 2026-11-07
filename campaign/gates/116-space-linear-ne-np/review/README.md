# Gate 116 executed evidence and publication limits

**Source, screen, review, publication and replay checks are complete.** The parent published
PR **#229** and ran the current-campaign replay: **2 modules, 0 failures, 0 static mismatches**.
`evidence/merged-tree/receipt.json` pins the exact source/snapshot. The user chose Codex for the
external audit; that gate remains open. **Not yet clear to merge.**

The pinned source base is the user's #228 merge. `source-freeze.json` gives its full checked
commit and the reviewed head content SHA-256. The source is the fixed
`lean/space-linear-ne-np` Hierarchy content; `screen/source-receipt.json` intentionally leaves
the final PR commit pending. The parent has matched every population head blob against the published PR and recorded
the replay in the separate `evidence/published-source-match.json` / `evidence/merged-tree/` receipts.

| Check | Actual result |
|---|---|
| Source declaration freeze | 47 → 47; 4 public / 43 private; only `SPACE_linear_ne_NP` body changes; every other declaration's complete text identical |
| Headers/visibility/order | All complete top-level-delimited headers, visibility and order unchanged; nested `input := x` parser control passes |
| Imports | Only the approved `SpaceComplexity.Padding` addition |
| Source size and admissions | 2505 → 2518 lines; source admissions 2 → 1, leaving only `space_universal` |
| Non-private compiled census | 4 → 5, including all internal auxiliaries |
| All-constant compiled census | 137 → 138; 133 private constants on both sides; no removal, kind change or module-owner move |
| Sole compiled addition | Internal theorem `Complexity.SPACE_linear_ne_NP._proof_1_1`; no new source API |
| Target/auxiliary axioms | Target uses standard three; auxiliary uses `propext`, `Quot.sound` |
| Direct foreign inventory | Four definitions: NP, SPACE, padLang, pairEncode; all sealed, no exclusions |
| Strong new-section seal | Exit 0, zero errors, only the unchanged F6 admission warning; four default-simp definition unfoldings removed |
| Positive controls | Four pointwise + four parameter-abstracted equations, all close unsealed, exit 0 |
| Negative controls | Same eight equations all fail sealed, exit 1; exactly one error at every expected source line, no extra diagnostics |
| Argument inspection | No foreign definition named in simp/rw/unfold; local equality is the sole explicit rewrite argument; published iff used |
| Campaign per-file lint | 0 FAIL / 1 inherited size WARN, unchanged |
| Policy per-file lint | Same two inherited findings: absent Main definitions heading and size; no new finding |
| Eleven-file copy-text screen | Eligible bodies 249 → 250; pairs 31 → 31; reproduced text 5,917 → 5,917; zero new/removed pairs |
| Current-campaign merged-tree replay | **Parent run passed: 2 modules, 0 failures/static mismatches; only F6 remains admitted** |
| External audit | **Pending user dispatch after publication** |

The source header and declaration comparisons are in `headers-*.json`, `source.diff` and
`source-freeze.json`. Source admission names are in `source-admissions.json`. All source/evidence
copies use `.lean.txt`; none are additional campaign Lean files.

`Inventory.lean.txt` is the primary accurately scoped target-plus-auxiliary inventory. The
parent's earlier `evidence/Metadata.lean.txt`, whose inherited E-PAD comments overdescribe its
later target filter, is preliminary. Do not use that prose as a whole-module inventory claim.

The strong seal concerns the newly changed target section, not the unchanged legacy Hierarchy
proofs. The same-home private consumer helper is byte-for-byte fixed. The four default-simp
definitions present in this closure are Action.apply, Cfg.init, MultiTapeTM.initCfg and
**NDTM.initCfg**; the strong source copy removes all four. Its earlier passing defaults-present
version is retained distinctly. `control-check.json` verifies error multiplicity and exits.

Both census views preserve generated/internal constants; the all-constant view also includes
private declarations. `constant-delta.json` and `all-constant-delta.json` reconcile both views.
They distinguish the single compiler auxiliary from the unchanged four public source results.

`screen/` contains both complete raw outputs, the identical full population lists, all full base
sources, per-run command/status/hash receipts, the pair delta and semantic classification. The
two screens ran serially under the shared screen lock and released it. Their head export differs
from the base at exactly the one approved source file. Candidate counts are not debt counts.

`REVIEW.md` and `receipt.json` preserve the initial internal review, written before the follow-up
screen request. `screen/receipt.json` and `followup.json` record the later screen/pack work, so the
initial no-screen scope is not mistaken for the final evidence state. No Git mutation, commit,
push, actual proof-worktree source edit, `lake build` or bare Lean check was performed here.

No blueprint file or public name binding changes. No strict global blueprint validation is
claimed; the policy's conditional requirement for edited blueprint material is not triggered.
`source-reference.md` provides the official indexed reproduction of the cited exercise, its short
excerpt and the direct-fetch limitation. It is not a claim of a visual PDF or full book audit.
