# Post-#234 scoped MIG integration preparation

**Not yet clear to merge: #233 — integration, actual validation and gate118 remain pending.**

#234 was merged by Seyoon at `bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c`, with exactly the gatedF1 Lean tree. The current pushed
MIG source was `b1f553b315f31b949076e91119473ce4070e7d53`. This folder is a read-only plan/scoped patch for those exact parents,
not a new fill or an applied source integration. The actual Git merge base is `93e191691318432578b44a06b7d1398ec143a533`;
3023 remains the earlier proof-comparison base and is not misrepresented as the merge base.

Two textual merge conflicts require mechanical preservation:

- **Catalog declaration modify/delete:** B1 retains the1043-byte improved redirect-space
  theorem while the campaign removes its old home. The broad conflict also contains old
  `f2_timed*` machinery that MIG already deleted. Preserve all MIG deletions; remove only
  the B1 duplicate theorem. Keep the exact gated1043-byte body in Wrappers, not the older
 1013-byte Catalog implementation. Its SHA256 is
  `3de684d6d30b02098aaf68c8b4223d9d8c92e2ff037505fdd3b5f494412baedf`.
- **Simulation concurrent insertion:** keep the B1 block. Its public branchTM_k/State rows
  equal the campaign rows byte-for-byte, and its private branchTM_initCfg_false/true proofs
  must remain. No new statement/API choice is required.

After root merges campaign and resolves those conflicts, validate the complete prospective
source hashes in captures/prospective-after-conflict-resolution. Then apply
`001-post-merge-consumer-bodies.patch`, the14 exact approved consumer replacements in6files.
The original15th change (Catalog duplicate deletion) is already discharged by conflict
resolution. Apply `002-approved-sketch-synchronization.patch` next: the previously approved
14 sketch updates and Catalog owner-index comment only. Neither patch uses old whole-file
after copies. They were constructed on the actual three-way source union and preserve every
publisher addition. `000-reference-campaign-api-merge.patch` and the combined B1 reference
patch are review aids, not instructions to reapply the campaign changes after merging.

The five LIVE-stop uses consume the merged arbitrary-predicate full-configuration fixed-entry
contract. Seven NONE-first-halt uses consume the pre-existing public theorem; none is silently
converted into a LIVE-stop instance. The two constant-space leaves cite the newly merged
pairDiag/incFixed zero-space equations. Names/headers/imports/machines/instances and other
MIG proof bytes are preserved; all17 previously filled targets stay untouched by these scoped
edits, and the complete WordSize source holding the3RAM residuals is byte-identical to B1.
The global redirect theorem remains once, in Wrappers. Exact API publisher/source bindings,
inert before/after captures and forward/reverse patch checks are recorded in this folder.

Root owns the actual campaign merge, scoped application, commit/push and strong validation:
actual owner/dependency chain on complete mac5 context; current owned AX/census; direct
argument review plus changed-region seals/paired controls; source/runtime/header freeze;
and a fresh merged-tree downstream replay, then the selected Codex gate118. The earlier
generation1 small native checks do not validate these integrated whole modules. Nine later
production rewrites remain source-only evidence until that execution; retained legacy reader
sites can still require routine mechanical fixes during root's strong seals. No new API/import,
debt/route/statement decision is identified by this preparation, and no new proof fill occurred.

No source/canonical/Git mutation, Lean, screen, snapshot/cache write, commit/push or dispatch
was performed. Only own inert scratch/output files were written. Supplied scripts were read
as data and not executed. A read-only inspection initially mistyped the env path and was
immediately rerun with the exact required environment before using its results; all final
preparation commands used the required env and Python-I. The own builder is retained as data.
