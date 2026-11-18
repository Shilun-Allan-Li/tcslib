# Codex audit · Gate 46 round 1 · the GSW 6b gate: O2 (#376) and the 6b statements (#377)

Audit two stacked draft PRs using pack.md:
- #376 (O2) at 04ba2446f541c39dd02aefaa97a9eb31dbbda748 (tree 8b615e06, on the records tip 38123ccb, whose Lean is
  olean snapshot #10): decodeLo, decodeHi and the proved interval reader decode_iff_mem_Ico in LWE/BitEncoding.lean,
  audited as a proof.
- #377 (statements) at 7563734a8badba842223e0687c719b3b4692e9d2 (tree c56db4c4, base #376): the 6b statements of GSW
  phase 6 (bootstrapping, circular security, the leveled scheme, the ratio and the asymptotic statements), with 24
  admitted targets, the two proved citations G11/L1, the reader-only G14/A2, every definition and reader, and the
  landing edits LE-6b1..3 (680be9fa) and LE-g46 (7563734a: the pre-dispatch sweep's S1 fixed, and the [Gen09]
  citations). Audit the statements' fidelity to BV14, BV11, AP14 (Alperin-Sheriff-Peikert
  bootstrapping), GSW13, Pei16 and Bar89 as the issued brief pins them, and to plan section r3 with the rulings; check
  the [Gen09] citations LE-g46 adds (question C3).

Campaign records are pinned at 1404eff9d9d9f55f7e4687a87395dec70dbb791e (RECORDS.txt), the commit that files the records copy of this pack; its parent
is the records tip 9ae6b909 or a records-only descendant, whose Lean equals snapshot #10's.

The evidence is the maintainer's: phase 1 (static) on the worker's delivery (exchange 3b340824; six commits reproduce
hash for hash) and phase 2 on snapshot #10 (R1 19 modules, R2 14 modules, rc 0; admissions 192 -> 216, exactly the 24
targets; sorryAx in exactly the 24 targets; strict and coe A/B seals on 12 owners with 0 errors; controls ALL_OK; unfold
scan 0 foreign; lint unchanged). The pre-dispatch duplication sweep (dup-sweep.md) found one item, S1; it was ruled
fix-now and fixed by LE-g46, whose recheck (le-g46.md: 8 modules rc 0, the same 24 targets, admissions 216, axioms
unchanged, coe-A 0 errors) is the only Lean run behind this re-staged pack.

- pack.md: pins, scope, what changed, the rulings in force, the audit questions A-I, the replays, the known slips, the
  merge interaction, the findings format.
- dup-sweep.md: the pre-dispatch duplication sweep (S1 and notes N1-N11).
- pr376.diff.txt, pr377.diff.txt: the PR views. pr377-le.diff.txt: the LE-6b1..3 commit.
- le-g46.md, le-g46.diff.txt, le-g46-evidence.zip: LE-g46, its diff and its evidence (inner SHA256SUMS).
- pr376-description.md, pr377-description.md: the PR bodies at re-staging.
- source-head.json: pins, every commit, and per-file hashes, line counts and widths.
- sources.zip: the 12 files at the head (7563734a), the 3 changed files at the base, the consumed phase-5, LWE, Regev and 6a
  files, the seven ingests (BV14, BV11, AP14, GSW13, Pei16, Bar89, Gen09) and the pinned Mathlib/core files the sweep
  names. Its README.md gives every entry's SHA-256 and origin.
- verification.zip: the staging's git-object checks with their scripts, the phase-1 and phase-2 evidence ZIPs (nested
  unchanged), the landing-edit diff, LE-g46's record and evidence, the records (reviews, phase 2, the checkpoint review, the issued brief package,
  plan section r3, rulings, policy, Gate 45 and 50 findings, decision-log and ledger extracts) and the PR REST fields.
  MANIFEST.md gives provenance; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the sweep, the reviews and records, the PR descriptions, the checks, the landing-edit, LE-g46 and
  O2 diffs, le-g46.md, the 12 Lean files at the head, the seven ingests, plan section r3 and policy.md. Each section header names its
  path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate46-gsw-6b-findings.md as Markdown in the chat, with findings
numbered G46-NN and a verdict per PR and overall of CLEAR or HOLD. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
