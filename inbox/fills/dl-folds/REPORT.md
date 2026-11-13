# Fill `dl-folds` — DL-36 and DL-37 folds and accepted promotions

**Status: checkpoint 3 (group E) delivered; checkpoints 1 (group G) and 2 (groups R, B, L)
delivered before.** The final checks follow; this report is extended at each delivery.
§1–§8 are the checkpoint-1 report (unchanged), §9 is checkpoint 2, §10 is checkpoint 3.

| | |
|---|---|
| Unit | `dl-folds` (brief `outbox/fills/dl-folds/brief.md`, exchange `a0a46d7c5`; `evidence/inputs/`, SHA256SUMS 7/7 OK) |
| Worker | Claude |
| Issue base | `d3f2290a2c66f614e8807903b89ac595086578b3` (merge of #298) on `cryptography/pass-shelat-ch2-4` |
| Branch | local `fill/dl-folds`; checkpoint 1 = `b3f7dae2c`, checkpoint 2 = `a2b3b3a4f`, checkpoint 3 = `5ad4c0775` (three commits on the base) |
| Toolchain | Lean 4.25.0, Mathlib of the base's `lake-manifest.json` |
| Order | base `order.txt` 421 modules; after checkpoint 1, `evidence/cp1/order-cp1.txt`, 422 modules; after checkpoint 2, `evidence/cp2/order-cp2.txt`, 422 modules |

## 1. Checkpoint 1 at a glance

- All seven G items are **done**: the listed copies are deleted (14 `NMSim` lemmas; `NMCCA2`'s
  `fwdHandler`, `fwdHandler_impl`, `exists_withAdviceOn`, `cntRead` and `ansRead` with their
  lemmas; the private PRF `impl_of_query`), their uses re-pointed, and the promoted lemmas
  published in the Games layer under new names (§3). No item is escalated.
- **Statements:** `decls2` over the 24 changed and new files: 28 ADDED, 23 REMOVED, **0 CHANGED**
  (`evidence/cp1/statements/decls2-cp1.tsv`). The audited endpoints are untouched (none of their
  files' headers changed; the endpoint files `Indistinguishability.lean` and `Simulation.lean`
  changed only in one proof line and in docstrings, §5).
- **Census** (public constants, base against checkpoint 1, name map applied): REMOVED 32 = the
  listed copies and their generated `simps` field lemmas and `congr_simp`; ADDED 41 = the promoted
  lemmas, the published readers, the generated lemmas of the moved definitions, and three
  generated matchers of the re-derived `ChallengeSim.expect_simulate_eager`; **CHANGED 1**, that
  re-derived proof's generated matcher `ChallengeSim.expect_simulate_eager.match_1_1` (a proof
  artifact, not a statement); REPOINTED 6 (types equal after the name map); map check 0 bad
  (`evidence/cp1/census/census-diff-cp1.txt`).
- **Build:** every module from the first edited one (`Games/OracleComp`, position 199) to the end of
  the recomputed order checked, 224/224 pass (`evidence/cp1/sweep.tsv`); after a last
  docstring-only edit, positions 286–422 rechecked, 137/137 pass (`evidence/cp1/sweep2.tsv`).
- **Sorry census:** 45 declarations in 24 modules, identical to `base-sorries.txt`
  (`evidence/cp1/sorry-census.txt`, `evidence/logs/sorry-census-base.txt`).
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`: 216 FAIL,
  103 WARN, the same FAIL and WARN lines as at the base (`evidence/cp1/lint-cp1.log`,
  `evidence/logs/lint-base.log`).
- **Rule 10 (early check):** whole-file seals A and B of 11 changed and new files pass with no
  failing declaration (`evidence/logs/seal/cp1/results.jsonl`, sources `evidence/seal-src/cp1/`).
  The full seal comparison (every changed file, base and final, controls, explicit-unfold scan)
  belongs to the final delivery.
- **Patch replay:** the series applied to the base gives the branch's tree
  (`evidence/cp1/patch-replay.log`).

## 2. Files (checkpoint 1)

| File | Lines base → cp1 |
|---|---|
| `Games/OracleComp.lean` | 331 → 371 |
| `Games/Simulate.lean` | 327 → 374 |
| `Games/Probability.lean` | 397 → 409 |
| `Games/Machines.lean` | 216 → 278 |
| `Games/BitCodec.lean` | 399 → 430 |
| `Games/Hopping.lean` | 445 → 524 |
| `Games/Efficiency.lean` | 844 → 935 |
| `Games/Forwarding.lean` (**new**) | — → 212 |
| `Games.lean` (facade) | 61 → 64 |
| `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean` | 315 → 369 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 702 → 673 |
| `NMI/Forward.lean` | 350 → 230 |
| `NMI/Decrypt.lean` | 350 → 298 |
| `NMI/Encrypt.lean` | 332 → 332 |
| `NMI.lean` (`Indistinguishability.lean`) | 655 → 655 |
| `NMS/Generic.lean` | 460 → 224 |
| `NMS/Rounds.lean` | 356 → 194 |
| `NMS/Challenge.lean` | 415 → 416 |
| `NMS/Hybrid.lean` | 683 → 683 |
| `NMS/SimIND.lean` | 912 → 911 |
| `NMS/Simulator.lean` | 628 → 628 |
| `NMS/Reduction.lean` | 661 → 661 |
| `NMS/IndSim.lean` | 293 → 293 |
| `Simulation.lean` | 795 → 796 |

Paths are relative to `TCSlib/Cryptography/`; `NMI/`, `NMS/` as in the brief. Every file stays below
1000 lines. `Games/Efficiency.lean` keeps 64 lines of room for the R1 readers of checkpoint 2.

## 3. Items of group G

The grep receipts (searches at the base, with hits) are in `evidence/grep/group-G.txt`
(script `evidence/tools/greps_g.sh`).

### G1 — budget reduction and `buildComp_of_ret` — done

- `NMSim.buildComp_of_ret` → `Games.buildComp_of_ret` (`Games/Machines.lean`, in section
  `BuildComp` beside `buildComp_zero_of_ret`, `buildComp_succ_of_ret`).
- `NMSim.buildComp_budget_eq` → `Games.buildComp_budget_eq`, beside `buildComp_costBoundedBy`.
- `NMSim.toCompOn_budget_eq` → `Complexity.NUPPT.toCompOn_budget_eq`, beside
  `NUPPT.toCompOn_costBoundedBy` (the namespace of the `NUPPT.toCompOn_*` lemmas of the file).
- Statements are the copies' up to the namespace; proofs unchanged. Uses re-pointed:
  `NMS/Simulator.lean` (`NUPPT.toCompOn_budget_eq`), `Rounds`' own uses moved with the lemmas.
- Further copies: none (receipts G1-budget, G1-ret).

### G2 — calls and finalizations — done

- **Published (Fin form)** beside `InteractiveHandler.impl_of_ret` in `Games/Efficiency.lean`:
  - `InteractiveHandler.impl_of_query`: answer `y' y` and state `s' y` as vectors, the general form
    of both `NMSim.impl_of_query` and the private PRF copy (any outer index `j`, any `perCall ≥ 1`);
  - `InteractiveHandler.finish_of_ret`: `finRun … = ⟨[true], ⟦b⟧⟩ → finish = pure b`.
- **The list forms are different statements** (lists `u`, `v`, `b` with length hypotheses and
  `padFin` in the conclusion), so they are kept as corollaries, derived from the Fin forms with
  `ofFn_padFin_of_length`:
  - `NMSim.impl_of_ret` → `InteractiveHandler.impl_of_ret_padFin`;
  - `NMSim.impl_of_query` → `InteractiveHandler.impl_of_query_padFin`;
  - `NMSim.finish_of_ret` → `InteractiveHandler.finish_of_ret_padFin`.

  They live in the new `Games/Forwarding.lean`, not beside `impl_of_ret`: with them
  `Games/Efficiency.lean` would pass 1000 lines once the R1 readers are added (935 lines now, plus
  about 45). Their statements are the NMSim copies' (same argument order), so the uses only change
  name: `NMS/Challenge.lean` (3), `NMS/Simulator.lean`, `NMS/Reduction.lean`.
- **Private PRF `impl_of_query`** (`OracleFromPRF/Handler.lean:421`) folded onto the published
  `InteractiveHandler.impl_of_query` (with `j = 0`, `perCall = 1` from `pkHandler_perCall`); its
  private helper `encodeLog_one`, used only there, is deleted. The three uses
  (`pkHandler_impl_enc`, `pkHandler_impl_dec_open`, `pkHandler_impl_challenge_none`) now open each
  round goal with `show pkRun q atkBit b _ = _` (the copy stated its hypotheses on `pkRun`
  directly) and, in the second round, `simp only [Fin.val_zero, List.replicate_zero]` (the
  published lemma writes the outer index of the log as `1^j`, the copy as `[]`). Nothing else in
  those proofs changed.
- Further copies (receipts G2-impl, G2-buildComp-use), not folded, recorded in §7:
  `AdaptiveCPA/Handler.lean` `acHandler_impl_forward` re-proves `impl_of_query` inline, and
  `pkHandler_finish`, `acHandler_finish` re-prove a return-at-budget-0 finalization inline. They
  are proofs of published theorems, not declarations, so the brief's rule that other proofs stay
  unchanged keeps them.

### G3 — `expect_toCompOn_outLen` — done

`NMSim.expect_toCompOn_outLen` → `Games.expect_toCompOn_outLen` (`Games/Efficiency.lean`, after
`exists_toCompOn_of_toComp`). Uses (`NMS/Simulator`, `IndSim`, `SimINDGap`) resolve to it through
`open TCSlib.Cryptography.Games` without a source change. No further copy.

### G4 — reasoning on the possible outputs, costs — done

| Copy | Promoted | Home |
|---|---|---|
| `NMSim.expect_congr_of_allOutputs` | `Games.ProbComp.expect_congr_of_allOutputs` | `Games/Hopping.lean`, after `expect_mono_of_allOutputs` |
| `NMSim.bind_congr_of_allOutputs` | `Games.OracleComp.bind_congr_of_allOutputs` | `Games/OracleComp.lean`, after `AllOutputs.bind` |
| `NMSim.costBoundedBy_bind_of_allOutputs` | `Games.OracleComp.CostBoundedBy.bind_of_allOutputs` | `Games/OracleComp.lean`, after `bind_congr_of_allOutputs` |
| `NMSim.expect_expect_sample` | `Games.ProbComp.expect_expect_sample` | `Games/Probability.lean`, section `Sampling` |
| `NMSim.simulate_costBoundedBy_once` | `Games.simulate_costBoundedBy_once` | `Games/Simulate.lean`, after `simulate_costBoundedBy` |

`CostBoundedBy.bind_of_allOutputs` cannot sit directly beside `CostBoundedBy.bind`: it needs
`AllOutputs`, which the file defines after the cost section; it is the last lemma of the
"Possible outputs" section, named in the `CostBoundedBy.bind` style. No further copies.

### G5 — one-shot coins drawn in advance — done

- `NMSim.expect_simulate_eager` (with its private helper `simulate_eq_of_used`) →
  `Games.expect_simulate_eager` (`Games/Hopping.lean`, new section "One-shot coins drawn in
  advance"; the helper stays private there).
- `ChallengeSim.expect_simulate_eager` keeps its name and statement (decls2: unchanged) and is now
  derived from it: with the coins `re` fixed, the CPA oracle becomes a deterministic oracle `OE re`
  (a local `let` defined by `match` in the proof) whose simulation is `chRun (g · re)` (induction);
  from the unchallenged state `Games.expect_simulate_eager` (used = "challenge recorded") gives the
  average; from a recorded state the oracle is already deterministic and `chRun_some_congr` removes
  the dependence on `re`. `ChallengeSim.lean` gains `import TCSlib.Cryptography.Games.Hopping`.
- Uses: `NMS/Hybrid.lean` resolves to the Games lemma unchanged; `PaddedCPA.lean` keeps using the
  ChallengeSim lemma.

### G6 — equal until bad in expectation — done

`NMSim.expect_eq_until_bad` → `Games.expect_eq_until_bad`, directly before `prob_eq_until_bad`.
`prob_eq_until_bad` keeps its statement (decls2: unchanged) and both conjuncts are now derived from
it: "`Q` and good" is `𝔼[if bad then 0 else 1_Q]`, and "bad" is `1 − 𝔼[if bad then 0 else 1]`
(`prob_not`). The private `expect_ite_one_split`, used only by the old second conjunct, is deleted.
Use re-pointed: `NMS/SimIND.lean` (resolves through `open Games`; docstrings qualified).

### G7 — the forwarding handler, hard-wired advice, log readings — done

- **New module `Games/Forwarding.lean`** (imports `Games.Efficiency`; module docstring; imported by
  the facade `Games.lean`, `## Contents` updated):
  - `NMCCA2.fwdHandler` (with its `simps` field lemmas `_stateLen`, `_seedLen`, `_perCall`,
    `_init`, `_advIn`, `_outLen`, `_finCall`, `_finRun`) → `Games.fwdHandler` (same lemmas);
  - `NMCCA2.fwdHandler_impl` → `Games.fwdHandler_impl`, now proved from
    `InteractiveHandler.impl_of_query` and the published `_input` lemmas of the readers;
  - `NMCCA2.exists_withAdviceOn` → `Complexity.NUPPT.exists_withAdviceOn` (it is a fact about
    `NUPPT`, like `NUPPT.exists_withAdvice`); proof unchanged;
  - the three list-form call lemmas of G2.
- **Why a new `Games/` module and not `Games/Efficiency.lean` or a sibling under
  `Games/Efficiency/`:** `Games/Efficiency.lean` would pass 1000 lines (§2). A sibling under
  `Games/Efficiency/` must import `Games.Efficiency` (it needs `InteractiveHandler`), so the
  facade `Games/Efficiency.lean` could not import it, and the lint would add a new FAIL
  ("facade does not import child module") for both `Games/Efficiency.lean` and `Games.lean`.
  Under `Games/` the facade `Games.lean` imports it, and the lint has no new FAIL.
- **Rule 10 and the definition's body:** `fwdHandler`'s round function, the private `fwdRun`,
  moved with it. It read the round input through `Forward`'s private readers `rState`, `rIdx`,
  `rQuery`, `rLog`, `rAns`; it now reads it through the published `InteractiveHandler.rS`, `rI`,
  `rX`, `rL` and the new `InteractiveHandler.rAns` (R3, published in this checkpoint because
  `fwdRun` needs it), with the same bodies. This is the only definition body that changed
  (recorded body change). `Forward`'s private readers and their private `fields_input`, used only
  by `fwdRun` and `fwdHandler_impl`, are deleted (they are R2's private copies).
- `NMCCA2.simulate_fwdHandler_impl` is not in the item list and stays in `NMI/Forward.lean` with
  its name; its statement now mentions `Games.fwdHandler` (re-pointed). The definitions that
  instantiate the handler, `NMCCA2.decHandler`, `NMCCA2.encHandler` and `NMSim.copyHandler`, are
  textually unchanged and now elaborate to `Games.fwdHandler` (census REPOINTED rows of their
  `eq_1` lemmas).
- `cntRead`, `ansRead`, `cntRead_eq`, `ansRead_eq`, `polyTimeComputable_cntRead`,
  `polyTimeComputable_ansRead` → `Games.*` in `Games/BitCodec.lean` (new section "Readings of a log
  entry"). `polyTimeComputable_cntRead` needs `Complexity.polyTimeComputable_isNil`, so
  `Games/BitCodec.lean` imports `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop` (§4).
  `length_logEmit_cntRead` and `logEmit_ansRead` stay in `NMI/Decrypt.lean` (they need `logEmit`,
  item E1). In `length_logEmit_cntRead` the hypothesis `cntRead [] = []` was `rfl`; `cntRead` is
  now another file's definition, so it reads `by rw [cntRead_eq]; rfl` (Rule 10).
- Uses re-pointed: `NMS/SimIND.lean` (`open NMCCA2 (…)` drops the moved names;
  `NMCCA2.fwdHandler_outLen` → `fwdHandler_outLen`), `NMI.lean`, `NMS/Simulator.lean`,
  `NMS/IndSim.lean` (`NUPPT.exists_withAdviceOn`), and docstrings.
- Further copies (receipts G7-*): the private `rY` (PRF handler) and `rFwd` (AdaptiveCPA handler)
  are R3 copies of the answer reader (checkpoint 2). `OracleFromPRF.lean:536` re-proves
  `polyTimeComputable_ansRead` as a local `have` inside a proof (§7).
  `DiscreteLogHardcore.lean:1130` `dlb_fα` has `ansRead`'s body but reads a field of a different
  layout, so it is not a copy.

## 4. Imports and order

| Module | Import change | Reason |
|---|---|---|
| `Games/BitCodec.lean` | + `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop` | `polyTimeComputable_isNil` for `polyTimeComputable_cntRead`; a Complexity module (order 67 < 225), no TCSlib.Cryptography import, so acyclic |
| `Games.lean` (facade) | + `TCSlib.Cryptography.Games.Forwarding` | the facade imports its new child; only `TCSlib.lean` imports `Games.lean`, so acyclic |
| `Games/Forwarding.lean` (new) | `TCSlib.Cryptography.Games.Efficiency` | `InteractiveHandler` |
| `OracleSecurity/ChallengeSim.lean` (consumer) | + `TCSlib.Cryptography.Games.Hopping` | `Games.expect_simulate_eager` |
| `NMI/Forward.lean` (consumer) | `Games.Efficiency` → `Games.Forwarding` | `Games.fwdHandler` |

No downstream module is imported to reach a lemma. The order is recomputed with a stable
topological sort of the base order (`evidence/tools/reorder.py`): `Games/Hopping` moves before
`ChallengeSim` (265 and 266), and `Games/Forwarding` is inserted at 280, before its first consumer
`NMI/Forward` (`evidence/cp1/order-cp1.txt`).

## 5. Statements, bodies and proofs

- `decls2` (`evidence/tools/decls2.py`, the maintainer's tool): 0 CHANGED over the 24 files.
- `bodies.py` (`evidence/tools/bodies.py`, complement to decls2: every definition's whole text and
  every private theorem's header, private declarations included):
  `evidence/cp1/statements/bodies-cp1.tsv` has no CHANGED-BODY and no CHANGED-PRIVATE-HEADER row;
  its REMOVED/ADDED rows are the moves of §3 (`fwdRun`'s body change from private to published
  readers is a move between files and is recorded in G7).
- Proofs that changed beyond re-pointed names, each required by its item:
  `Games.prob_eq_until_bad` (G6), `ChallengeSim.expect_simulate_eager` (G5), the three PRF handler
  proofs (G2), `NMCCA2.length_logEmit_cntRead` (G7, Rule 10), and the moved `fwdHandler_impl` (G7).
- The audited endpoint files `NMI.lean` and `Simulation.lean`: one proof line of
  `nmSecure_cca2_of_indSecure_cca2` re-pointed (`exists_withAdviceOn` →
  `NUPPT.exists_withAdviceOn`) and docstrings re-pointed; no header changed.

## 6. Name map (checkpoint 1)

`evidence/census/namemap.tsv` is the cumulative map (old full name → new full name), checked
against the census (`MAP-CHECK`: every old name absent at head, every new name present). Short
form (NMSim = `Composability.NMSim`, NMCCA2 = `Composability.NMCCA2`, `IH` =
`Games.InteractiveHandler`):

| Old | New |
|---|---|
| `NMSim.buildComp_budget_eq` | `Games.buildComp_budget_eq` |
| `NMSim.toCompOn_budget_eq` | `Complexity.NUPPT.toCompOn_budget_eq` |
| `NMSim.buildComp_of_ret` | `Games.buildComp_of_ret` |
| `NMSim.impl_of_ret` | `IH.impl_of_ret_padFin` |
| `NMSim.impl_of_query` | `IH.impl_of_query_padFin` |
| `NMSim.finish_of_ret` | `IH.finish_of_ret_padFin` |
| (private) `PRFGame.impl_of_query` | `IH.impl_of_query` |
| (private) `PRFGame.encodeLog_one` | — (helper of the deleted copy) |
| `NMSim.expect_toCompOn_outLen` | `Games.expect_toCompOn_outLen` |
| `NMSim.expect_congr_of_allOutputs` | `Games.ProbComp.expect_congr_of_allOutputs` |
| `NMSim.bind_congr_of_allOutputs` | `Games.OracleComp.bind_congr_of_allOutputs` |
| `NMSim.expect_expect_sample` | `Games.ProbComp.expect_expect_sample` |
| `NMSim.costBoundedBy_bind_of_allOutputs` | `Games.OracleComp.CostBoundedBy.bind_of_allOutputs` |
| `NMSim.simulate_costBoundedBy_once` | `Games.simulate_costBoundedBy_once` |
| `NMSim.expect_simulate_eager` | `Games.expect_simulate_eager` |
| (private) `NMSim.simulate_eq_of_used` | (private) `Games.simulate_eq_of_used` |
| `NMSim.expect_eq_until_bad` | `Games.expect_eq_until_bad` |
| (private) `Games.expect_ite_one_split` | — (unused after G6) |
| `NMCCA2.fwdHandler` and its 8 `simps` lemmas, `fwdHandler.congr_simp` | `Games.fwdHandler` and the same lemmas |
| (private) `NMCCA2.fwdRun`, `polyTimeComputable_fwdRun` | (private) `Games.fwdRun`, `polyTimeComputable_fwdRun` |
| `NMCCA2.fwdHandler_impl` | `Games.fwdHandler_impl` |
| (private) `NMCCA2.rState`, `rIdx`, `rQuery`, `rLog`, `rAns` | `IH.rS`, `rI`, `rX`, `rL`, `rAns` |
| (private) `NMCCA2.fields_input` (Forward) | `IH.rS_input`, `rI_input`, `rX_input`, `rL_input`, `rAns_input` |
| `NMCCA2.exists_withAdviceOn` | `Complexity.NUPPT.exists_withAdviceOn` |
| `NMCCA2.cntRead`, `cntRead_eq`, `polyTimeComputable_cntRead` | `Games.cntRead`, `cntRead_eq`, `polyTimeComputable_cntRead` |
| `NMCCA2.ansRead`, `ansRead_eq`, `polyTimeComputable_ansRead` | `Games.ansRead`, `ansRead_eq`, `polyTimeComputable_ansRead` |

New declarations without a predecessor: `IH.impl_of_query` (also the PRF copy's successor),
`IH.finish_of_ret`, `IH.rAns`, `IH.rAns_input`, `IH.polyTimeComputable_rAns`.

## 7. New duplication found (not folded)

1. `AdaptiveCPA/Handler.lean` `acHandler_impl_forward` re-proves `InteractiveHandler.impl_of_query`
   inline (`buildComp_succ_of_query`, then `buildComp_zero_of_ret` with `Fin.append`).
2. `pkHandler_finish` (`OracleFromPRF/Handler.lean`) and `acHandler_finish`
   (`AdaptiveCPA/Handler.lean`) re-prove a returning finalization inline (`buildComp_zero_of_ret`),
   the content of `InteractiveHandler.finish_of_ret`.
3. `OracleFromPRF.lean:536` proves `PolyTimeComputable fun z => pairSndD (pairSndD (pairFstD z))`
   as a local `have`, which is `Games.polyTimeComputable_ansRead`.

Each is inside the proof of a published theorem; the brief keeps other proofs unchanged, so they
are listed for a later cleanup.

## 8. Evidence (checkpoint 1)

`evidence/SHA256SUMS` lists every evidence file, and the delivered evidence paths are exactly the
manifest's paths (checked by `evidence/tools/pack.py`).

| Path | Content |
|---|---|
| `inputs/` | the brief's inputs (brief, addendum, README, `order.txt`, `roots.txt`, `base-sorries.txt`, their SHA256SUMS) |
| `logs/preflight.log`, `cache-*.log`, `packages-check.log`, `mathlib-roots.txt` | environment and narrowed cache fetch (addendum) |
| `logs/bootstrap.tsv`, `logs/bootstrap/` | the base bootstrap, 421/421 |
| `logs/census/census-base.log`, `logs/census/axioms-base.log` | base census (13,639 constants) and base axioms of the 46-file superset |
| `logs/seal/base/` | base whole-file seals A/B, scans, `results.jsonl` (46 files) |
| `logs/lint-base.log`, `logs/sorry-census-base.txt` | base lint and sorry census |
| `cp1/order-cp1.txt`, `cp1/changed-modules.txt` | recomputed order; changed and new modules |
| `cp1/sweep-list.txt`, `cp1/sweep.tsv`, `cp1/sweep-logs/` | checkpoint sweep 199–422 |
| `cp1/sweep2-list.txt`, `cp1/sweep2.tsv`, `cp1/sweep2-logs/` | recheck 286–422 after docstring edits |
| `cp1/sorry-census.txt` | 45 in 24, as at the base |
| `cp1/census/census-cp1.log`, `cp1/census/census-diff-cp1.txt` | census and its comparison |
| `cp1/statements/decls2-cp1.tsv`, `bodies-cp1.tsv` | statement and body comparison |
| `cp1/lint-cp1.log`, `cp1/patch-replay.log` | lint; patch replay |
| `logs/seal/cp1/`, `seal-src/` | early seals of 11 files; all seal sources |
| `census/namemap.tsv` | cumulative name map |
| `grep/group-G.txt` | grep receipts |
| `tools/` | every script used (`chk.py`, `sweep.py`, `reorder.py`, `sorrycensus.py`, `census_diff.py`, `decls2.py`, `bodies.py`, `seal.py`, `files.py`, `greps_g.sh`, `gen_census.py`, `pack.py`) and the census sources (`tools/census/`) |

## 9. Checkpoint 2 — groups R, B, L

### 9.1 At a glance

- R1, R2, R3, B1, B2, L1, L2, L3, L4: **done**. B3: **escalated** (both aliases kept, §9.4).
- **Build:** recomputed order `evidence/cp2/order-cp2.txt` (422 modules). Three sweeps, all
  passing: 160–422 after the R/B/L edits (`cp2/sweep.tsv`, 263/263), 262–422 after docstring and
  `open` edits (`cp2/sweep2.tsv`, 161/161), and 205–422 after the GGM fold
  (`cp2/sweep3.tsv`, 218/218). Every module from the first edited one (`Foundations/BitLists`,
  position 160) to the end passed after its last edit.
- **Sorry census:** 45 declarations in 24 modules, identical to the base (`cp2/sorry-census.txt`).
- **Lint:** 216 FAIL (the base's lines), 102 WARN: one WARN fewer than the base, because
  `ZeroKnowledge/ThreeColoring/Machines.lean` drops from 1007 to 998 lines (`cp2/lint-cp2.log`).
- **Census** (`cp2/census/census-diff-cp2.txt`, 34 changed and new modules, cumulative name map):
  REMOVED 106 (the listed copies, their generated auxiliaries, and the checkpoint-1 removals),
  ADDED 70, **CHANGED 1** (the generated matcher of the re-derived
  `ChallengeSim.expect_simulate_eager`, as at checkpoint 1), REPOINTED 40 (types equal after the name
  map), every removed name in the map, map check 0 bad.
- **Statements:** `decls2` over the 34 files: 52 ADDED, 78 REMOVED, **13 CHANGED**; all 13 are equal
  to the base header after the textual re-pointing `rdU→rU`, `rdState→rS`, …, `finU→rU`, `finSt→rS`,
  `chunkAt→coinBlock` (`cp2/statements/decls2-cp2-modmap.txt`: SAME-MODULO-MAP 13, DIFFERENT 0;
  tool `tools/decls2_map.py`). The 24 changed definition bodies and private headers
  (`bodies-cp2.tsv`) are likewise all re-pointings only (`bodies-cp2-modmap.txt`: 24/24). No header
  of the owned files `NMI.lean` and `Simulation.lean` and no endpoint changed; see §9.5 for the
  question this raises.
- **Rule 10 (early check):** seals A and B of 16 changed files (`logs/seal/cp2/`): no failing
  declaration except `Asymptotic/EnsemblesLemmas.lean`, whose 10 failing declarations are exactly the
  base's (`logs/seal/base/results.jsonl`), so none is new.
- **Patch replay:** the two patches applied to the base give the branch's tree
  (`cp2/patch-replay.log`).

### 9.2 Files changed at checkpoint 2 (base → checkpoint 2, lines)

| File | Lines |
|---|---|
| `Foundations/BitLists.lean` | 105 → 179 |
| `Asymptotic/Adversary.lean` | 373 → 452 |
| `Asymptotic/EnsemblesLemmas.lean` | 865 → 887 |
| `Games/BitCodec.lean` | 399 → 444 |
| `Games/Efficiency.lean` | 844 → 979 |
| `Authentication/Signatures/Lamport.lean` | 581 → 567 |
| `Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean` | 265 → 254 |
| `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` | 573 → 572 |
| `Encryption/PrivateKey/OracleFromPRF/Handler.lean` | 702 → 672 |
| `Encryption/PublicKey/AdaptiveCPA/Handler.lean` | 543 → 542 |
| `ZeroKnowledge/ThreeColoring/Machines.lean` | 1007 → 998 |
| `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean` | 450 → 440 |
| `NMI.lean` | 655 → 646 |
| `NMI/Forward.lean` | 350 → 156 |
| `NMI/Decrypt.lean` | 350 → 318 |
| `NMI/Encrypt.lean` | 332 → 345 |
| `Simulation.lean` | 795 → 797 |
| `NMS/Generic.lean` | 460 → 200 |
| `NMS/Rounds.lean` | 356 → 45 |
| `NMS/Hybrid.lean` | 683 → 575 |
| `NMS/Challenge.lean` | 415 → 450 |
| `NMS/Simulator.lean` | 628 → 636 |
| `NMS/Reduction.lean` | 661 → 682 |
| `NMS/Recover.lean` | 519 → 520 |
| `NMS/SimIND.lean` | 912 → 913 |
| `NMS/IndSim.lean` | 293 → 294 |

Every file stays below 1000 lines (`Games/Efficiency.lean` 979). Some NM files grew because the
deleted bundle lemmas `fields_input`, `fields_finInput`, `polyTimeComputable_rd` and
`polyTimeComputable_finFields` are replaced by one `have` per field from the published per-reader
lemmas, and the published names are brought in with `open … (…)` lists.

### 9.3 Items

The grep receipts are in `evidence/grep/groups-RBL.txt` (script `tools/greps_rbl.sh`).

**R1 — finalization readers: done.**
- Beside `InteractiveHandler.finInput` (`Games/Efficiency.lean`, new subsection "Readers of a
  finalization input"): `rU_finInput`, `rZ_finInput`, `rW_finInput`, `rS_finInput`, `rL_finInput`;
  the new reader `InteractiveHandler.finA` (`finA w = pairFstD (pairSndD (pairSndD w))`) with
  `finA_finInput` and `polyTimeComputable_finA`.
- Deleted: `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL` and their `_eq`, `fields_finInput`,
  `polyTimeComputable_finFields` (`NMI/Forward.lean`); `NMSim.finSt`, `finSt_eq`, `finSt_finInput`,
  `polyTimeComputable_finSt` (`NMS/Simulator.lean`).
- Re-pointed: the private `dCnt`, `dCt`, `dIn`, `dFin` (`NMI/Decrypt.lean`) and `eBit`, `eMsg`,
  `eTape`, `eCt` (`NMI/Encrypt.lean`); the nm-sim finalizations `simFin`, `simOutL`, `nmFin`,
  `nmOutL` and SimIND's private `copyFin`, with their proofs.

**R2 — round-input readers: done.** Deleted `NMSim.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`,
`rdQuery`, `rdLog` with their `_eq`, and the bundle lemmas `NMSim.fields_input` and
`NMSim.polyTimeComputable_rd` (`NMS/Rounds.lean`); uses re-pointed to `InteractiveHandler.rU`, `rZ`,
`rW`, `rS`, `rI`, `rX`, `rL` and their `_input`/`polyTimeComputable_` lemmas in `NMS/Challenge`,
`Simulator`, `Reduction`. `Forward`'s private `rState`, `rIdx`, `rQuery`, `rLog` were removed at
checkpoint 1 with `fwdRun`. The handler-specific private `fields_input` lemmas of the PRF and
AdaptiveCPA handlers read their state fields as well; they are not copies and stay.

**R3 — the answer reader: done.** `InteractiveHandler.rAns` (published at checkpoint 1) gains
`rAns_eq`. Re-pointed: `NMSim.rdAns` and `rdAns_input` (deleted; → `rAns`, `rAns_input`), the
private `rFwd` (AdaptiveCPA handler; deleted, `acRun` reads `rAns`) and the private `rY` (PRF handler;
deleted, `rCt` and `pkRun` read `rAns`; the private `rY_one` now states `rAns w = y` and reads it
through `rAns_eq`).

**B1 — `chunkAt` onto `coinBlock`: done.** `NMSim.chunkAt`, `chunkAt_eq`, `length_chunkAt` deleted;
every use re-pointed to `coinBlock`, `coinBlock_eq`, `length_coinBlock` (definition bodies
`realView`, `idealView`, `nmOutL`, `simOutL` included; `length_chunkAt _ _ _ h` becomes
`length_coinBlock h`, whose block arguments are implicit).

**B2 — block lemmas and the block window: done.**
- Beside `coinBlock` (`Asymptotic/Adversary.lean`): `coinBlock_flatten` (Lamport's
  `Authentication.coinBlock_flatten`, moved, statement unchanged, now `TCSlib.Cryptography.
  coinBlock_flatten`), `map_coinBlock_flatten` (NMSim's `map_chunkAt_flatten`, now derived from
  `coinBlock_flatten` entry by entry: the two were the same fact), `coinBlock_flatten_append`
  (NMSim's `chunkAt_flatten_append`).
- The block window is `FunFamily.ofFn_blocks` (reused, not re-proved). Derived from it, statements
  unchanged: `ofFn_block_eq_coinBlock` (NMSim's `ofFn_block`, with a tail, beside
  `FunFamily.ofFn_blocks`), `NMCCA2.ofFn_nthCt` (`NMI.lean`; proof only),
  `EnsembleLemmas.take_drop_ofFn_blocks` (proof only), `MultiMsg.take_drop_ofFn_blocks`
  (`ReductionMachine.lean`; now `(FunFamily.ofFn_blocks …).symm`), and, found by the grep,
  `GGM`'s public `drop_take_ofFn_blocks` (`GGM/Evaluator.lean`; it re-proved the window element by
  element; now `rw [Nat.mul_comm ℓ k, FunFamily.ofFn_blocks]`). `OneWay.ofFn_block_eq_take_drop`
  already was a corollary of `FunFamily.ofFn_blocks`.
- Not exact copies, so kept: `take_eq_flatten_chunkAt` and `drop_flatten_append` (`NMS/Hybrid.lean`;
  the first now reads `coinBlock`, its name is unchanged because renaming is not allowed).
- Further window facts found and left (receipt B2): the private `Primality.ofFn_chunk`, `ColRep`'s
  `drop_take_ofFn_blockRead` (both already corollaries of the published `ofFn_drop_take`), the
  private `Factoring.fac_ofFn_halves` (already a corollary of `OneWay.ofFn_block_eq_take_drop`),
  `HardCoreLoops.take_drop_blocksStr` (a different definition, `blocksStr`), the GIZK `Closeness`
  field readers (a different layout); Complexity files (`NPPoly`, `PSubsetPPolyTableauCorrect`) are
  out of scope.

**L1 — lists: done.** In `Foundations/BitLists.lean`: `flatMap_range_drop` (the general form of
both private copies, `NMS/Generic.lean` and `NMI/Forward.lean`; Forward's `logEmit_encodeLog` now
instantiates it with `fun l => G (codec.encodeLog l)`), `ofFn_natAdd_eq_drop`, `decide_map_ofFn`,
`ofFn_eq_map_range` (three copies deleted: NMSim's, `ColMachines.ofFn_eq_map_range`, whose one use
passes `fun t => h t t.isLt`, and `GI.ofFn_eq_map_range`), `length_flatten_map_const` (now
`List.length_flatten`, `List.map_const'` and `List.sum_replicate_nat`, as the brief asks), and
`length_flatten_map_range` (NMSim's, needed by `coinBlock_flatten_append`; same Mathlib route).
Mathlib has none of the others as stated. Further copies outside scope: `Codec/Valid.lean`'s
`ofFn_eq_map_range` and `NPPoly`'s `flatMap_range_drop_take` (Complexity files).

**L2: done.** `NMSim.padFin_append_split` → `Games.padFin_append_split` (`Games/BitCodec.lean`,
beside `padFin_nil`; `padFin` itself is in `Asymptotic/Adversary.lean`). It has no use after G2.

**L3: done.** `NMSim.seedEquiv`, `seedEquiv_ofFn`, `seedEquivPoly`, `seedEquivPoly_ofFn` →
`EnsembleLemmas.*` beside `coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean`, 887 lines).

**L4: done.** The statements agree up to the namespace (`List.ofFn (padFin k a) =
EnsembleLemmas.padL k a`), so `NMSim.ofFn_padFin_eq_padL` is deleted and its uses re-pointed to
`EnsembleLemmas.ofFn_padFin_eq_padL`.

`NMS/Rounds.lean` keeps only `length_ofFn_coins`, which the brief keeps local; its module docstring
now says where the rest went.

### 9.4 B3 — escalated: both `blocks` aliases kept

Probe `evidence/b3/B3Uses.lean` (run on the oleans of all 421 modules, output
`evidence/b3/b3-uses.log`): every constant whose type, definition body or proof mentions
`EnsembleLemmas.blocks`, `blocks_eq`, `blocks_apply`, `blocks_symm_apply` or the private
`Ensemble.blocks`/`blocks_eq` of `Asymptotic/Ensembles.lean`.

- **Statements that mention `EnsembleLemmas.blocks`** (folding would change them):
  - theorem headers: `EnsembleLemmas.exists_copiesRed`, `EnsembleLemmas.ofFn_blocks_symm`,
    `EnsembleLemmas.take_drop_ofFn_blocks` (Asymptotic, ch. 2–4),
    `CommitmentLemmas.ComLoop.emit_init_of_lt` (ZeroKnowledge, ch. 4);
  - a definition body: `PRFGame.pkTapes` (`OracleFromPRF/Handler.lean`).
  - (the alias's own lemmas `blocks_eq`, `blocks_apply`, `blocks_symm_apply`).
- **Proofs only** (would only be re-pointed): `ColRep.pushesUniform_blockRead`,
  `PRFGame.ofFn_pkTapes`, `PRFGame.pkTapes_apply`, `Ensemble.Indist.copies`,
  `MultiMsg.take_drop_ofFn_blocks`, the private `owpComStr_eq_loopOut` (Commitment).
- **The private alias of `Ensembles.lean`** is in the body of the definition `Ensemble.copies` and in
  its `eq_1` lemma; its documented purpose is that definition.
- **Obstruction:** the four headers and the two definition bodies are audited ch. 2–5 statements;
  a fold changes their text (and, for `pkTapes` and `Ensemble.copies`, the body) from the alias to
  `FunFamily.blocks`. The alias is public, so the body change is not the allowed private→published
  reader change.
- **Smallest correction:** a gate approval to restate `exists_copiesRed`, `ofFn_blocks_symm`,
  `take_drop_ofFn_blocks` and `ComLoop.emit_init_of_lt` with `FunFamily.blocks` and to re-point the
  bodies of `pkTapes` and `Ensemble.copies` (all definitionally equal: `blocks_eq` and the private
  `blocks_eq` are `rfl`); the aliases and their three lemmas can then be deleted with no proof
  change beyond re-pointing.

### 9.5 Header re-pointing in the NM helper files (decision for the reviewer)

Folding R1, R2 and B1 re-points names that the headers of 13 NM helper theorems and the field types
of `NMSim.ChalParams` mention (`decls2-cp2-modmap.txt`): `chalRun_eq`, `realView_eq`,
`idealView_eq`, `take_eq_flatten_chunkAt`, `recView_nmOutL`, `altMsg_eq`, `nmFin_eq`, `nmOutL_eq`,
`nmOutput_eq_entryTails`, `simCt_eq`, `simFin_eq`, `simMsg_eq`, `simOutL_eq`. Each is the base header
with the deleted reader or block name replaced by its published successor (`rdU`→`rU`, …,
`chunkAt`→`coinBlock`), and the census shows their types equal after the name map. I read "every
theorem of the NM files that Gates 06, 18 and 19 audited" as the owned files `NMI.lean` and
`Simulation.lean` (whose headers are byte-identical) and the endpoints. If the gates' audit is meant
to cover these helper headers byte for byte, R1, R2 and B1 cannot be folded without an alias, and
the smallest correction is to accept these 13 re-pointed headers.

### 9.6 Imports (checkpoint 2)

| Module | Import change | Reason | Acyclic |
|---|---|---|---|
| `Foundations/BitLists.lean` | + `Mathlib.Data.Fintype.Basic` | the decidable equality of `Fin k → Bool` in `decide_map_ofFn`'s statement | Mathlib only |
| `Asymptotic/Adversary.lean` | + `TCSlib.Cryptography.Foundations.BitLists` | `length_flatten_map_range` for `coinBlock_flatten_append` | `BitLists` imports only Mathlib |
| `Games/BitCodec.lean` | + `Mathlib.Data.List.GetD` | `List.getD_append`, `getD_append_right` in `padFin_append_split` | Mathlib only |
| NM consumers | `open TCSlib.Cryptography.Games.InteractiveHandler (…)`, `open TCSlib.Cryptography.EnsembleLemmas (…)` | the re-pointed names | no import |

The recomputed order places `Foundations/BitLists` (160) before `Asymptotic/Adversary` (161).

### 9.7 Definition bodies changed (re-pointing only)

Private → published reader (the allowed kind): `PRFGame.pkRun`, `PRFGame.rCt` (`rY`→`rAns`),
`AdaptiveCPA.acRun` (`rFwd`→`rAns`), `NMCCA2.dCnt`, `dCt`, `dIn`, `dFin`, `eMsg`, `eTape`, `eCt`
(`fin*`→`rU`/`rZ`/`rW`/`rL`/`finA`). Public copy → published successor (the deleted copies' uses):
`NMSim.ChalParams` (field types), `chalRun`, `realView`, `idealView`, `altMsg`, `nmFin`, `nmOutL`,
`nmParams`, `simCt`, `simFin`, `simMsg`, `simOutL`, `simParams` (`rd*`/`fin*`/`finSt`→`r*`,
`chunkAt`→`coinBlock`, and inside `nmParams`/`simParams` the polynomial-time fields read from
`polyTimeComputable_rU`, `_rX`, `_rAns` instead of projections of `polyTimeComputable_rd`). All 24
are identical to the base after the name map (`bodies-cp2-modmap.txt`).

### 9.8 Name map (checkpoint 2)

The rows are appended to `evidence/census/namemap.tsv` ("checkpoint 2" block and its generated
auxiliaries). `-` marks a deleted declaration without a successor of its own: the `_eq` lemmas of
the deleted readers (their published successors have `_input`/`_finInput` lemmas instead; no use
needed them) and the bundle lemmas `fields_input`, `fields_finInput`, `polyTimeComputable_rd`,
`polyTimeComputable_finFields` (each use reads the published per-reader lemmas).

## 10. Checkpoint 3 — group E

### 10.1 At a glance

- E1, E2, E3: **done**; nothing escalated.
- **Build:** order unchanged from checkpoint 2 (`cp3/order-cp3.txt`). Sweep of positions 253–422
  from the first edited module (`Encryption/PublicKey/OracleSecurity`), 170/170
  (`cp3/sweep.tsv`); recheck of 281–422 after a docstring rewrap in `NMI/Forward.lean`, 142/142
  (`cp3/sweep2.tsv`).
- **Sorry census:** 45 in 24, as at the base (`cp3/sorry-census.txt`). **Lint:** 216 FAIL (the
  base's lines), 102 WARN (§9.1) (`cp3/lint-cp3.log`).
- **Census** (36 changed and new modules): REMOVED 110, ADDED 83, CHANGED 1 (the same generated
  matcher as before), REPOINTED 40, map check 0 bad, every removed name mapped
  (`cp3/census/census-diff-cp3.txt`).
- **Statements:** `decls2` 13 CHANGED, all the checkpoint-2 re-pointings (13/13 SAME-MODULO-MAP).
  Definition bodies: 24 re-pointings and the 2 intended E1 redefinitions (§10.2): `NMCCA2.logEmit`
  and `NMSim.chunkMap` (`cp3/statements/bodies-cp3-modmap.txt`).
- **Patch replay:** three patches, the branch's tree (`cp3/patch-replay.log`).

### 10.2 Items

**E1 — iterate and emit: done.**
- New, beside `relabelN` (`Games/Efficiency/OracleBridge.lean`, 321 → 410 lines, in namespace
  `TCSlib.Cryptography.Games` before the `EffFill` history translator):
  - `iterEmit step emit m x = (List.range m).flatMap fun i => emit (step^[i] x)`, with `iterEmit_eq`;
  - `length_iterate_le_add`: if one step never makes a word longer than `max |y| c`, the orbit stays
    within `|x| + c`;
  - `polyTimeComputable_iterEmit`: `fun x => iterEmit step emit (|x| + 1) x` is polynomial-time,
    from `Complexity.polyTimeComputable_iterateEmit` (read-only, used as is) with the orbit bound
    of `length_iterate_le_add`;
  - `iterEmit_encode`: on `enc l`, for an encoding whose step drops the first element and whose
    emission reads it, `m ≥ |l|` rounds emit `l.flatMap g` (from `flatMap_range_drop`, L1).
- **Instances** (definition bodies changed to the instance; types unchanged; definitional
  equality by unfolding `iterEmit`):
  - `NMCCA2.logEmit G L := iterEmit pairSndD G (|L| + 1) L`. `logEmit_eq` keeps its statement and
    now reads `iterEmit_eq` (not `rfl`: Rule 10); `polyTimeComputable_logEmit` and
    `logEmit_encodeLog` keep their statements and are corollaries of `polyTimeComputable_iterEmit`
    (`c = 0`) and `iterEmit_encode` (encoding `codec.encodeLog`). The private
    `length_iterate_pairSndD_le` and `iterate_pairSndD_encodeLog` are deleted (their content is
    `length_iterate_le_add` and the iterate step of `iterEmit_encode`); `length_le_length_encodeLog`
    stays.
  - `NMSim.chunkMap c f x := iterEmit (chunkStep c) (chunkEmit c f) (|x| + 1) x`. `chunkMap_eq`,
    `polyTimeComputable_chunkMap` and `chunkMap_flatten` keep their statements and are corollaries
    of `iterEmit_eq`, `polyTimeComputable_iterEmit` (`c = 2`, the private `length_chunkStep_le`)
    and `iterEmit_encode` (encoding `l ↦ ⟨ctx, l.flatten⟩`). The private
    `length_iterate_chunkStep_le` is deleted.
- **`relabelN` and `relabel` are kept** (they are the efficiency fill's T4 definitions, audited at
  Gate 10; `relabelN` also has a round-count argument of its own). Bridging equations, proved through
  `iterEmit_eq`: `EffFill.relabelN_eq_iterEmit : relabelN m w = iterEmit pairSndD relabelEmit m w`
  and `EffFill.relabel_eq_iterEmit : relabel x = iterEmit pairSndD relabelEmit (|x| + 1) x`.
  `bridgePre_poly` keeps its statement and is now a corollary of `polyTimeComputable_iterEmit`
  (its private orbit bound is gone). `relabelN_encodeHist` and `length_le_length_encodeHist` are
  unchanged (their statements are about `relabelN` with any `m ≥ |L|`). No foreign body was needed.
- **Further iterate-and-emit constructions found** (receipt E1-*), not folded: their round count
  is a polynomial other than `|x| + 1` or their definitions are in audited ch. 2–4 files:
  `BlockEncryptor.blockEncFun`, `decListFun`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`'s
  `prgIter`, `CommitmentLemmas.ComLoop`, the ZK `EncodingMachines` counter loops. Also two public
  copies of one fact in ZK: `GI.iterate_pairSndD_encodeMsgs` (`GraphIsomorphism/EfficiencyRep.lean`)
  and `ColMachines.iterate_pairSndD_encodeMsgs` (`ThreeColoring/Machines.lean`) — new duplication,
  outside this unit's items.

**E2 — `polyTimeComputable_guessBit`: done.** `NMSim.polyTimeComputable_guessBit`
(`NMS/Recover.lean`) → `NMCCA2.polyTimeComputable_guessBit` (`NMI/Encrypt.lean`, after
`guessBit_eq`); the private `polyTimeComputable_guessFun` is now `polyTimeComputable_guessBit`
composed with the reader of `w`. Recover reaches it through its `open NMCCA2 (…)` list.

**E3 — done.** `NMSim.ctLen_pos` (`NMS/Recover.lean`) and `NMCCA2.indImpl_eq_of_msgLen_eq_zero`
(`NMI/Encrypt.lean`) → `FixedLengthPKScheme.ctLen_pos` and
`FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero` (`Encryption/PublicKey/OracleSecurity.lean`,
723 → 765 lines, new subsection at the end of `FixedLengthPKScheme`; statements unchanged up to the
namespace, proofs unchanged, read through the published `_onSpec` equations). Uses:
`NMS/Recover`, `NMS/IndSim` (`S.ctLen_pos …`) and one proof line of the endpoint
`indSecure_cca2_of_nmSecure_cca2` in `NMI.lean` (`S.indImpl_eq_of_msgLen_eq_zero …`; header
unchanged).

### 10.3 Files changed at checkpoint 3 (base → checkpoint 3, lines)

| File | Lines |
|---|---|
| `Games/Efficiency/OracleBridge.lean` | 321 → 410 |
| `Encryption/PublicKey/OracleSecurity.lean` | 723 → 765 |
| `NMI.lean` | 655 → 647 |
| `NMI/Encrypt.lean` | 332 → 331 |
| `NMI/Forward.lean` | 350 → 140 |
| `NMS/Generic.lean` | 460 → 181 |
| `NMS/Recover.lean` | 519 → 495 |
| `NMS/IndSim.lean` | 293 → 294 |

No import changes at checkpoint 3 (`OracleBridge` reaches `Foundations/BitLists` through its
existing imports).

### 10.4 Name map (checkpoint 3)

| Old | New |
|---|---|
| `NMSim.polyTimeComputable_guessBit` | `NMCCA2.polyTimeComputable_guessBit` |
| `NMSim.ctLen_pos` | `FixedLengthPKScheme.ctLen_pos` |
| `NMCCA2.indImpl_eq_of_msgLen_eq_zero` | `FixedLengthPKScheme.indImpl_eq_of_msgLen_eq_zero` |
| (private) `NMCCA2.length_iterate_pairSndD_le`, `iterate_pairSndD_encodeLog` | — (`Games.length_iterate_le_add`, `Games.iterEmit_encode`) |
| (private) `NMSim.length_iterate_chunkStep_le` | — (`Games.length_iterate_le_add`) |

New: `Games.iterEmit`, `iterEmit_eq`, `length_iterate_le_add`, `polyTimeComputable_iterEmit`,
`iterEmit_encode`, `EffFill.relabelN_eq_iterEmit`, `EffFill.relabel_eq_iterEmit`.
