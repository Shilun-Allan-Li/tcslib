# Claude job · duplication consolidation DL-30 to DL-34 (`dl-consolidation`)

**Issue base** `b96ab3ccc1915497ea3138df499eec00b6581db0` on `cryptography/pass-shelat-ch2-4` (the merge of #293).
**Unit** `dl-consolidation`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib
revision in that commit's `lake-manifest.json`.

This job repays the duplication debt that Seyoon accepted during the four CPA-pilot fills and the private-key
CPA/CCA1 fill. The debt is recorded as rows DL-30 to DL-34 of `briefs/pass-shelat-ch5-8/duplication-ledger.md`.
Read those five rows first.

The job is a **refactor with no mathematical change**:
- promote each generic lemma to its shared home;
- delete the copies;
- re-point every use.

No audited statement changes.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/dl-consolidation` at the exact issue base,
  and record the base in `REPORT.md`. Keep the branch local.
- Read `policy.md` (§1 file layout, Rule 10 and abbreviations; §3 docstrings), the attached environment addendum
  and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/dl-consolidation/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: every changed or new file;
  - `evidence/`.
- Commit as `fill dl-consolidation: checkpoint N` and `fill dl-consolidation: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by
  a maintainer PR for Seyoon's approval.

## The items

Paths are relative to `TCSlib/Cryptography/`. **Grep first:** for every item, search the whole library at the
base for further copies under other names, including private ones. List each copy you find, then fold it in or
record why not. One case is known: the private `dlc_ofFn_padFin` in `Encryption/PublicKey/ElGamal.lean` belongs
to DL-31, and the public `Collection.ofFn_padFin_of_le` may already cover it.

### P · `Games/Probability.lean` (namespace `Games.ProbComp`)

| Item | Now | Action |
|---|---|---|
| P1 | `ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`; DL-30) | Promote all four. |
| P2 | `ChallengeSim.expect_sample_prod` (DL-30) | If it is `Bridge.expect_sample_pair` restated, delete it and re-point its uses. Otherwise keep it in ChallengeSim. |
| P3 | `expect_sample_update`, in two forms with the same name: `AdaptiveCPA` (`Encryption/PublicKey/AdaptiveCPA/Hybrid.lean`) and `BitwiseSim` (`Encryption/PublicKey/BitwiseCPA/Eager.lean`) (DL-32/33) | Promote one general form, deriving the other from it if both shapes are needed. Distinct names are required. |
| P4 | `PRFGame.abs_expect_sub_le` (`Encryption/PrivateKey/OracleFromPRF/Collision.lean`; DL-34) | Promote. |

### S · `Games/Simulate.lean`, or the lowest Games module whose imports cover the statement

| Item | Now | Action |
|---|---|---|
| S1 | `AdaptiveCPA.simulate_eq_of_abs` (Hybrid) and its generalization `PRFGame.simulate_eq_of_abs_bounded` (`OracleFromPRF/Reduction.lean`) | Promote the bounded form. Derive the other from it, or re-point its uses and delete it. |
| S2 | The `castImpl` family (`AdaptiveCPA/Hybrid.lean`) | Promote with its readers. |
| S3 | `PRFGame.expect_simulate_congr` (`OracleFromPRF/Games.lean`), `BitwiseSim.expect_simulate_eager` (Eager) | Promote. |

### H · `Games/Hopping.lean` (namespace `Games.ProbComp`)

| Item | Now | Action |
|---|---|---|
| H1 | `PRFGame.prob_bad_le`, `PRFGame.expect_sample_mem_le` (Collision) | Promote. `prob_bad_le` is the per-query potential bound, `Pr[bad] ≤ q·(size + q)·δ`. |

### A · beside `padFin`, `decodeFin` and `FunFamily.blocks` (`Asymptotic/Adversary.lean`), or `Games/BitCodec.lean`

| Item | Now | Action |
|---|---|---|
| A1 | `ofFn_padFin_of_length`: `GGMRed` public in `Pseudorandom/Functions/Asymptotic/GGM/Run.lean`, copy in `Asymptotic/HardCoreGLColl.lean`, ElGamal's private copy (DL-31) | Promote one public lemma, or reuse `Collection.ofFn_padFin_of_le` if it subsumes it. Delete all copies. |
| A2 | `ofFn_cast` (public, `AdaptiveCPA/Games.lean`), private `cca2OfFn_cast` (`Encryption/PrivateKey/OracleFromPRF.lean`) (DL-32) | Promote one. |
| A3 | `padFin_ofFn_zeroBits` (`AdaptiveCPA/Games`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (`OracleFromPRF/Transfer.lean`) | Promote beside `padFin`. |
| A4 | Private `ofFn_padFin_eq_padL` in both `AdaptiveCPA/Handler.lean` and `OracleFromPRF/Handler.lean` | Promote one public lemma beside `padL` (`Asymptotic/EnsemblesLemmas.lean`). |
| A5 | `AdaptiveCPA.ofFn_acTapes` and its re-proof `PRFGame.ofFn_pkTapes` (DL-34) | Add the generic `List.ofFn (blocks q ℓ ω j) = ((List.ofFn ω).drop (j·ℓ)).take ℓ` beside `FunFamily.blocks`. Derive both from it. |
| A6 | `BitwiseSim.decodeFin_nil_getD` (`BitwiseCPA/QueryHandler.lean`) | Promote beside `decodeFin`, or into `Games/BitCodec.lean`. |

### R · published readers beside their definitions

| Item | Now | Action |
|---|---|---|
| R1 | `indCodec_eq_bitCodec`, public-key in `AdaptiveCPA/Games` and private-key in `OracleFromPRF/Transfer` (DL-32/34 reader requests) | Publish one reader in `Encryption/PublicKey/OracleSecurity.lean` and one in `Encryption/PrivateKey/OracleSecurity.lean`. Delete the helper copies. |
| R2 | Reader request `hybridPre_eq` (DL-33) | Add it beside `hybridPre` in `Encryption/PublicKey/HybridMachine.lean`. Re-point BitwiseCPA's reading of `hybridPre`. |
| R3 | `BitwiseSim.expect_simulate_indImpl_cpa`, a public near-copy of the private lemma in `Encryption/PublicKey/OracleSecurity.lean` | Publish the OracleSecurity lemma under that name, with a docstring. Delete the copy. |
| R4 | `BitwiseSim.padded_enc_runAt`, `_coins` (Eager) | Move beside the padded readers in `Encryption/PublicKey/OracleSecurity.lean`. |
| R5 | `chRun_toCompOn_transport_list` (QueryHandler), which generalizes `ChallengeSim.chRun_toCompOn_transport` | Move the general form into ChallengeSim and derive the old lemma from it. Keep the old name and statement. |
| R6 | Private round-input readers `rU`…`rCnt`, `impl_of_ret` and `replicate_one`, in both `AdaptiveCPA/Handler.lean` and `OracleFromPRF/Handler.lean` (DL-34) | Publish one set beside `InteractiveHandler.input` in `Games/Efficiency.lean` (or in `List`, for `replicate_one`, if core lacks it). Delete both copies. |
| R7 | Length vectors `recDin/recDout` (`OracleSecurity/RecordHandler.lean`), `acDin/acDout` (`AdaptiveCPA/Handler`), `qDin/qDout` (QueryHandler) | If they are one function up to parameters, publish one and re-point. Otherwise record "not a copy" with the reason. |

### L · a shared list and vector module

Create one new module, `Foundations/BitLists.lean`. It imports Mathlib only, unless an existing upstream module
fits better; check this first and justify your choice. Promote into it:
- `headD_drop`: `BitwiseSim` (`BitwiseCPA/Planted.lean`) copies the public `CommitmentLemmas.headD_drop`, and
  `Pseudorandom/NextBit.lean` has the private `headD_drop_ofFn`. Keep one public lemma and delete the others.
- `flatten_ofFn_singleton` (Planted), with the private `flatten_ofFn_one` (`SecureComputation/Yao.lean`).
- `headD_ofFn_one` (`AdaptiveCPA/Games`).
- `zipWith_xor_cancel_left` (`OracleFromPRF/Lazy.lean`).
- `xorPerm`, with `_apply` (`OracleFromPRF/Collision.lean`). `ctOf_xorPerm` stays.
- `mem_keys_of_lookup_isSome` (Collision): replace it with core's or Batteries' `List.lookup_isSome_iff`, or the
  equivalent at the pin, if one exists. Otherwise promote it.

`ofFn_splitHalf_fst/_snd` (`AdaptiveCPA/Games`) read `splitHalf`. Move them beside `splitHalf` in
`Encryption/PrivateKey/OracleSecurity.lean` as readers.

### O · leftovers in the owned files

| Item | Now | Action |
|---|---|---|
| O1 | Private `ofFn_half` and `bitwise_runAtL` (`Encryption/PublicKey/BitwiseCPA.lean`) re-prove published facts (DL-33) | Use the published ones. |
| O2 | Private overlaps between `PRFStep` and the `cca2*` helpers in `Encryption/PrivateKey/OracleFromPRF.lean` | Merge them. |

## Rules

- **No statement changes.** No existing declaration other than the listed copies may change its statement,
  name, attributes or visibility. The exceptions are the listed publications (R1–R6, a private lemma made
  public) and the promoted lemmas, which get their new names. All proofs elsewhere stay unchanged except for
  re-pointed lemma names. Each gate-audited theorem keeps its statement byte for byte.
- **Deleting copies.** Delete them; no deprecated aliases (precedent: #192). Re-point every use in the library,
  `audits/` included.
- **Names.** Choose names in the home namespace (for example `Games.ProbComp.expect_sample_equiv`, `padFin_nil`).
  The report's census maps every old name to its new name.
- **Docstrings.** Public promoted lemmas keep or gain a formula docstring, and a sketch when nontrivial (policy §3).
  Generic lemmas need no [PS10] tag. Update every module docstring's `## Contents` or main-results list that
  names a moved declaration.
- **Imports.** You may add imports to consumer files. An import added to an existing Games, Asymptotic or
  Foundations module must be acyclic and listed in the report with its reason. Do not create a cycle. Do not
  import a downstream module to reach a lemma.
- **Rule 10.** A promoted lemma reads only definitions of its new home file, through their bodies, or other
  files' definitions through published readers. Where a lemma's proof read its old file's definitions, rewrite it
  through readers or stop (see Escalation). Generated matchers and projections count.
- **Simp.** Add no `@[simp]` and do not change global simp sets.
- **Size.** Keep every file below 1000 lines.
- **Out of scope.**
  - Every file outside `TCSlib/Cryptography/`, except `audits/` uses.
  - Notably the Arora–Barak files (`TCSlib/Complexity/…`), and other campaigns' files.
  - The duplicate `blocks` in `Asymptotic/EnsemblesLemmas.lean` and the private `blocks` in
    `Asymptotic/Ensembles.lean`: record them, but do not fold them.
- **Escalation.** An item may not be promotable without a Rule-10 violation, an import cycle or a statement
  change. If so, leave it, record the exact obstruction and the smallest correction, and continue. A checkpoint
  must still compile.

## Checkpoints

1. Groups P, S, H (Games layer).
2. Groups A, L (padFin, blocks, the list module).
3. Groups R, O.

Send the final delivery with full evidence.

## Checks and report

- **Bootstrap and sweep.** Bootstrap from `order.txt` (406 modules) and the narrow `roots.txt` per the addendum,
  one module per `scripts/lean_check_tree.sh` call, one Lean process per olean tree. Insert any new module before
  its first consumer, and recompute the order if imports change.
  - At each checkpoint, rebuild every edited module and everything after it in the order.
  - At the final delivery, run a full fresh sweep with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt`: there must be **no change** (48 in 26 modules).
- **Census.** Compare all declarations of the changed files, base against final, by name, type and attributes.
  Report:
  - removed (the listed copies only);
  - added (the promoted lemmas, readers and new module);
  - changed (expected 0, apart from listed visibility changes);
  - the old → new name map.
- **Axioms.** Print the axioms of:
  - every stored constant of every changed or new file;
  - the campaign endpoints: `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`,
    `INDSecure.adaptive_cpa`, `bitwise_padded_cpa`, `exists_adaptive_cpa`, `padded_cpa`, and both
    `Implications.PublicKey` entries.

  Expect only `propext`, `Classical.choice` and `Quot.sound`, as at the base. List any constant that changed
  axioms.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with base controls,
    and paired controls that pass unsealed and fail sealed.
  - Run the explicit-unfold scan of every changed file.
  - The Gate 17 audit's `PolyExpr.eval` remark applies: report the seal with and without it sealed.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`. Allow no new FAIL
  versus the base.
- **Grep receipts.** For each item, give the search you ran for further copies and the hits.
- **Report.** Give:
  - the base, the per-item disposition (done / not a copy / escalated);
  - changed and new files with line counts;
  - the import changes;
  - the census and name map;
  - the evidence;
  - the new duplication found.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**
