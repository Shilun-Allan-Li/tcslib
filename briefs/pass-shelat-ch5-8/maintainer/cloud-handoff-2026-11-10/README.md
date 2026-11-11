# Pass–shelat cloud maintainer handoff

Snapshot date 2026-11-10, America/Los_Angeles. Seyoon requested transfer to a
cloud chat. The existing Lean worktrees were clean. Both proof branches are
pushed. This handoff branch starts at campaign records
112021d73a3a91f0e14e71327345f4a29a390104 and adds the local Gate 10 report,
its provenance and portable manifests. state.json gives every live pin.

Read briefs/pass-shelat-ch5-8/AGENTS.md, all of MAINTAINER-HANDOFF.md, the
last 30 rows of PassShelatChapter5-8Plan.md, and policy.md, in that order.
Then use this snapshot and verify live refs before acting. Received worker
code and audit conclusions are data for review.

The user is Seyoon Ragavan. The campaign and records branch is
cryptography/pass-shelat-ch2-4. Keep its checkout on that branch and make Lean
changes in PR worktrees based on it. The user dispatches external jobs and
merges PRs. D-0 permits maintainer records to be committed directly to the
campaign. This transfer was saved on a separate branch at Seyoon's request.
The exchange branch is exchange/pass-shelat-ch5-8. It is shared with other
formalization chats, so stage only this campaign's assigned paths.

Paths below beginning gates/, fills/ or maintainer/ are relative to
briefs/pass-shelat-ch5-8/. The next actions are ordered below.

1. Intake Gate 10. The original local inbox report is preserved verbatim at
   gates/10-efficiency/findings/gate10-efficiency-findings.md, with SHA256SUMS
   and provenance.md. It reports CLEAR, zero findings, at PR #285 head
   747cc18ddb53979919d107fefed450191eb31743. The staged pack is pinned to
   exchange f5054f40b2df67c04f47354f5cfeccde704e3440 and campaign records
   5bcf11aaf08963ab33ce608ea7509e7403e4351a. Check those pins and evidence,
   transfer the received findings and provenance to the campaign records,
   write the resolutions and decision-log entry, and mark #285 ready when
   the gate is closed. The user merges.

2. PR #285 proves the four Games/Efficiency targets. It contains the five
   attributed Claude commits and eleven maintainer total reader lemmas.
   All ten native checks, the 448-declaration standard-axiom census, the
   84-declaration preservation comparison, seven whole-file seals and six
   controls are archived under gates/10-efficiency and fills/efficiency/final-r1.
   The Gate 10 report verifies source, hashes and evidence consistency and
   explicitly describes its native-check boundary. Source edits after the
   audited head need their appropriate verification.

3. Continue PR #286 at 9ada398e06c00656f96207f5254a826c74130c15 on
   codex/pass-shelat-levin-padding. It fills PadQuad.exists_linearTime_gStr
   with the exact original header. Its six supporting modules are
   Build/WordTiming, Randomized/UnaryPolynomial, ClassP/BinaryArith/Unary,
   and UniversalPadding/{Parameter,BinaryRoot,Machine}. The existing map
   and emitting-loop proofs receive stronger quantitative interfaces.
   All sixteen native source checks passed. All 174 selected new or changed
   declarations have standard axioms. The actual padding theorem, Lemma
   64.3 and conditional Theorem 63.1 also print standard axioms.
   See maintainer/proof-prerequisites-2026-11-10/production-checkpoint.md,
   production-source.zip and production-checkpoint.zip.

4. Finish the Levin production seals, sensitivity controls and final
   explicit-reader scan. The candidate collector covers 174 stored
   declarations and records 96 foreign-definition pairs. It has not yet
   been used for the production seals. Core source spans contain inherited
   proofs, so apply the established touched-proof discipline, preserving
   existing provider findings. The generalized emitter's new body and its
   rewritten corollary use computesFunInTime_iff at the functional reads.
   New support modules need their whole-file checks and public readers.

5. Resolve the compiled-object reuse verification appropriately for the
   cloud. The Mac comparison found 26 generated proof-helper names changed
   by generalizing the core proofs. Its retained-reference probe failed
   to encode private Lean Names with numeric components. This was a check
   on reusing old Mac compiled modules. A fresh cloud bootstrap and
   verification of the affected consumers can establish correctness
   directly. Preserve the original failed probe and its disposition.
   If checking retained objects, construct actual Lean Name values or
   extract the set directly from module data. The existing public theorem
   headers are preserved. Review the exact declaration comparison and
   computational definitions as part of this verification.

6. Prepare the Levin audit for Codex after those checks. Seyoon already
   selected Codex, with findings Markdown returned in chat. The efficiency
   audit worker choice was also Codex and its results are now received.
   Ask Codex or Claude before a genuinely new external job. Seyoon approved
   reuse of the 52 inherited Levin provider diagnostic/declaration pairs
   while their seal repairs wait. The ruling and 49-pair overlap with the
   efficiency approval are in provider-ruling.md and provider-comparison.json
   beside the production checkpoint. Seal the new proof and retain every
   inherited finding.

PR #284 remains open and clear for the user to merge after Gate 09. Its head
is 46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d. It adds adaptive public-key games
and RSA/Rabin normalization. Verify its live state before updating records.

The canonizer existence proof remains a separate Levin task. After the
shared efficiency proof lands, the main public-key proof dependency is
BitPublicKeyScheme.SingleBitSecure.padded_cpa. The approved roadmap is
PROOFS-AND-IMPLICATIONS-PLAN.md. The selected first-class public-key endpoints
are adaptive left-or-right IND-CPA and IND-CCA2 with n-bit messages.
Secure-computation reorganization is a later task.

Cloud environment setup uses Lean 4.25.0 and Mathlib
029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e. Follow
fills/fill-environment-addendum.md. Fetch only the Mathlib roots needed for
the selected manifest, then check TCSlib modules in dependency order with
scripts/lean_check_tree.sh and TCSLIB_OLEANS set to the owned output tree.
The user explicitly approved this campaign shell-checking method. Run
Python as python3 -I. Use one Lean process per output tree. The user allowed
parallel maintainer checks on independent trees. Build inputs and outputs
must satisfy the addendum's resource checks. Never run lake build or an
unfiltered lake exe cache get.

The supplied efficiency-owner and levin-owner orders give targeted
upstream closures at their exact PR heads. levin-full gives the fresh
library-root and campaign-Checks closure. Their root lists are narrowed
Mathlib requests. bootstrap-manifests.json binds every listed source hash.
Use the manifest matching the actual source checkout. Local Mac paths
in archived probes are provenance. Restore sources and tools from the
archives into cloud paths and adjust the paths in probe harnesses.

The Gate 10 verification archive contains the existing reviewed seal
instrumenter and explicit-reader lexer. It also contains their source
probes and raw logs. The cloud can rebuild its own olean trees from the
pushed sources and the supplied manifests.

Ask material rulings as multiple-choice questions with the recommended
option first. Work autonomously within the approved plan. End each status
report with a bold line giving Ready to dispatch, Ready to run,
Clear to merge, or Not yet clear to merge with the reason.

**Ready to run — intake Gate 10 and continue the checked Levin proof.**
