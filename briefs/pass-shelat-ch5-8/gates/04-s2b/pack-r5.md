# Gate 04 (Pass–shelat ch. 5–8, S2b), round 5: closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
at its head `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`, against the current base `7018d13e243df4d8b54b99444c34c934199755f5`
(`cryptography/pass-shelat-ch2-4`, which now contains #210, the equation-lemma PR closed by gate 07, and
the fill landings #224–#226).
- **The PR's diff against the base:** 26 files (25 under `TCSlib/` plus `TCSlib.lean`),
  `+2723 −287` (`evidence-r5/pr.diff.txt`, `pr-files.txt`).
- **The repair since round 4's head `a588adfed01eefe6971abd0846e3938ad02e8624`:**
  - the first-parent commits are in `evidence-r5/commits-since-r4.txt`;
  - the diff of the 26 files is in `evidence-r5/repair.diff.txt`;
  - the commits include merges of #210's rounds and of the merged base. Their effect on these
    files is #210's additions to `ZeroKnowledge/Interaction.lean` and `Foundations/Experiments.lean`
    (audited by gate 07).

**What changed in the approach since round 4.** The user ruled R-04-5 (A), **zero exclusions**:
- every read of another file's definition, in a statement, a definition body or a proof, goes
  through a published lemma;
- the equations #195's files needed from other files were added by #210;
- #195 re-points every read and adds equations beside its own definitions.

Round 4's R4-01 (twelve declarations with changed ambient binders that kept exclusions) is
therefore resolved by having **no exclusions at all**: `unseal.json` is `{}`, derived from an empty
seed over all 26 files. Notation by the user's rulings, never sealed: `PolyExpr.eval` (Q1),
`glNeed`, and the abbreviations `QueryImpl` and `OracleSpec.add` (R-04-4).

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF page − 12.

- **The deliverable:** **`gate04-s2b-r5-findings.md`**, committed as
  `inbox/gate04-s2b-r5-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and
  pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase`
  before pushing, never force-push, no PR).

The bundle holds this pack, then the files named below under `## ===== <path> =====` headers. The
full evidence folder (`gates/04-s2b/evidence-r5/`, including `tools/`, the candidate tables and the
per-file seal outputs) is on the records branch at the commit the prompt names.

## Brief for the auditor

1. **Verify round 4's resolutions** (`findings/gate04-s2b-r4-findings.md`, `resolutions-r4.md`): for
   R4-01, R4-02 and F02, say fixed, recorded or not resolved, and why.
2. **Zero exclusions.** Do the seal, the plain seal, the `$BASE` control and the scan show that no
   declaration in the 26 files reads another file's definition?
   - `seal-table.md`, `seal-evidence.log`, `seal-plain.log`, `seal-control-base.log`, `scan.log`,
     `scan-base.log`, `exclusions.md`, `unseal.json`, `seed-empty.json`.
   - Are the candidates collected from the elaborated terms of every declaration, with private names
     and compiler-generated matchers included (`candidates/`, `tools/collect*`, `tools/declx.py`)?
   - Is dropping `PolyExpr.eval` and `glNeed` (`tools/unsealable.py`) the only exception?
   - Does the scanner read `nth_rw`, `nth_rewrite` and multi-line `unfold`, and generated
     equation-lemma references (`tools/scan.py`)?
   - #210's sweep listed 16 rows in these files (`sweep-rows.tsv`). Each must pass the head seal
     and fail the control.
3. **The classifier** (`declchanges.tsv`, `tools/declx.py`, `tools/run_sigdump.sh`,
   `sig/`). Does it detect changes that come from ambient `variable` binders or universes, as at
   `Pseudorandom/Functions/{Defs,GGM,SubHybrids}.lean`, by comparing elaborated signatures?
4. **Restatements and re-proofs:**
   - `NUPPT.runAt_preComp` and `prfScheme_multiEncDist` now take their coins through published
     equivalences (`NUPPT.preComp_coinsEquiv`, `prfScheme_coinsEquiv`, with `_ofFn` lemmas). Is each
     the same proposition as before? Does every consumer still prove what it did?
   - The bodies of `PRG.doubling` (`Fin.cast` along `PRG.expand_stretch`) and `prfScheme.correct`:
     are they the same values?
   - The new equations beside #195's definitions:
     - `GGM.lean`: `ggm_apply`, `prefixAt_apply`, `splitHalves_apply_fst/snd`, `ggmBits_def`;
     - `PRF.lean`: `decodeOracleMove_*`, `encodeHist_eq_histEnc`;
     - `PRFLemmas.lean`: `preComp_coinsEquiv`, `eq_blocks_divNat_modNat`;
     - `MultiMessage.lean`: `prfScheme_coinsEquiv`.

     For each, check that it states exactly the definition, is public, is not `@[simp]`, and has a
     docstring with the formula.
   - The statement diff against round 4's head (`stmtdiff-vs-merge.txt`) and the later rounds
     (`r7/`–`r10/stmtdiff-*`).
5. **Merges.** The `Interaction.lean` resolution kept #210's `Protocol.transcriptWith_eq`/`outV_eq`
   (identical statements on both sides) and #195's `Strategy.out_eq`. Is anything lost or duplicated
   in the 26 files?
6. **Checks.**
   - Replay: `replay-865b2ba0.log`, `replay-final.log`, `r10/replay.log` (108 modules downstream of
     the changes since `f4b2c95d`, the landed fills included, plus Checks) and
     `r10/replay-extra.log` (23 more modules anywhere downstream).
   - Axioms: `axioms.log`, 198 public theorems.
   - Lint: `lint.log`.
   - The only `sorry`s in #195's files are the efficiency fill's targets in `Games/Efficiency.lean`.
7. **Reproducibility.** Can the classification, collection, derivation and seal be re-run from
   `tools/` and the inputs? Note what is not reproducible.
8. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r5/`; worker reports `WORKER-REPORT*.md`)

- **Seal:** 26/26 PASS with no named entries; plain seal 26/26; `$BASE` control (`27ae72da`, its
  rebuilt tree) FAIL in 16 files; the round-3 union check 5/5.
- **Scan:** 0 lemma-list hits, 0 `show`/`change` steps at seal failures, 0 equation-lemma
  references at the head, against 84/5/21 at the base.
- **Replay:** every module downstream of the merges and repairs, on the landed base, plus
  `audits/pass-shelat/Checks`. All rc 0, 0 errors.
- **Axioms:** 198 public theorems in the 8 files changed since `40553944`, all within `propext`,
  `Classical.choice`, `Quot.sound`.
- **Lint:** `style_lint` 0 findings over the 26 files; no file over 1000 lines.
- **Classifier:** SAME 279, ADDED 210, CHANGED 152, INDUCED 4 against the merge base.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R4-01: fixed / recorded / not resolved — <reason>` (also R4-02, F02).
Severity guide as in rounds 1–4. The gate closes at **0 blockers and 0 majors**.
