This is the landing PR for the pairing fill `bb1-machine` (`PairingCryptographyPlan.md`). It proves **T4** `exists_bb1_distinguisher` (`AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`), the reduction machine behind Boneh–Boyen BB1's selective-ID security from DBDH [BB04, §4.2]. It follows the route Gate 40 checked (the G40-03 sampler).

**Head:** `89a18a8225be1b76166af12a15179da291747783`. **Base:** `cryptography/pass-shelat-ch2-4`.

## Changes (8 files, against the tip)
- **Helper modules** under `IdentityBased/BonehBoyenMachine/`: `Draws`, `Words`, `Handler`, `Reduction` and `Oracles`. They hold the exponent sampler, the handler on encodings, the tape run, the reduction lemmas and the per-call glue. Every file stays under the 1000-line cap.
- **`BonehBoyenMachine.lean`** gains its helper imports, a `## Contents` section, T4's proof and a refreshed proof sketch. T4's header and statement prose are byte-identical.
- **The seven approved readers** (Seyoon, 2026-11-16, minimal form) are pure insertions into the frozen files:
  - three in `Defs.lean`: `IBEScheme.oracleImpl_{zero,one,two}_onSpec`;
  - four in `BonehBoyen.lean`: `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` and `ofFn_bb1SimCt`.

  Removing them restores both files byte for byte.

## Commits (7, all SSH-signed)
- Three in-house checkpoint commits (`7c0a55e0` lineage).
- The external worker's three commits: the readers, the `Oracles` helper, and T4.
- **LE-bb1m** `89a18a82`: in `Oracles.lean`, an unused `have` is removed and a docstring's arguments are put in Lean order (BM-F01, BM-F02). No proof changes.

## Review (`briefs/pairings/fills/bb1-machine/final-r1/review.md`): ACCEPT WITH LANDING EDITS
- **Phase 1 (static).**
  - 0 blockers, 0 majors, 1 minor (fixed by LE-bb1m), 8 info.
  - The patch series reproduces, and the readers are verbatim.
  - decls2 shows +8 / 0 / 0, and admissions remove only T4.
  - The worker's evidence recounts clean: seals 32/32 with 0 errors; controls with 314 sealed negatives, each failing once.
- **Phase 2 (Lean, on the maintainer's tree; `final-r1/phase2/`).**
  - **Replay on olean snapshot #4** (after #351 and #352): 12/12 modules rc 0. The state check is OK over 1427 modules.
  - **Admissions:** −1, exactly T4.
  - **Axioms:** T4 and the readers use the standard axioms only. `bb1_sidSecure` now reaches exactly T2 and T3.
  - **Rule 10:** the full run gives seals 32/32 with 0 errors, and the paired controls are ALL_OK, including the `Oracles` control probe (BM-F03). Seal inputs are unchanged on snapshot #4, and canonical coe-A was re-confirmed 8/8.
  - **Explicit-unfold scan:** 0 foreign unfolds.
  - **Lint:** no new FAIL or WARN.
- **Joint check with #340 on snapshot #4** (tree `33681cb8`, Lean-equal to `c7be1301`):
  - 16/16 modules rc 0, admissions −2;
  - the five owners downstream of `Assumptions` re-sealed 20/20 with 0 errors.

## Gate
**Gate 44 (Codex)** audits this PR together with #340. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA