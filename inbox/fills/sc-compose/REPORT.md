# Fill `sc-compose` · final · `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose`

**Worker** Claude. **Unit** `sc-compose` ([Gol04, §7.3.1, Theorem 7.3.3], the semi-honest composition
theorem). **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` (`cryptography/pass-shelat-ch2-4`), read from the
exchange at `2b9270ad095e993b020cb5e447d5a0043496802a` (pack 7/7 and SOURCE 152/152 verified:
`evidence/logs/inputs-check.log`). **Proof branch** `fill/sc-compose` (local), twelve commits over the base;
head `d3f405d4671a3ad0ffd3930ef182a43cb12ed134`. Checkpoints 1 and 2 were delivered at exchange `419c4ceb9` and
`f1ba0b1ac`.

| commit | content |
|---|---|
| `a3cb219da` … `32f837d9e` | checkpoint 1 (four commits): `composeP_efficient`, `composeV_efficient` |
| `2d99291eb` … `392a95ecb` | checkpoint 2 (four commits): the simulators, the output clause, the statistical switch |
| `756cb2c88eb2c99ce7b1b01f2502ba9480a36048` | five helpers (steps 3–5) and the proof of `hbcSecure_compose`; module title, `## Main results`, the theorem's sketch |
| `93afd4f35306371e201ea11ac8dd376efc3312ec` | Rule-10: read `Protocol.transcript`, `acceptProb`, `distAdv` through their published readers (found by the seals) |
| `034f90a97d75d2f2fa012438b7b0ffc70b13f5c2` | Rule-10: `exists_viewP_le`, `exists_viewV_le` with explicit length facts (found by the seals) |
| `d3f405d4671a3ad0ffd3930ef182a43cb12ed134` | proof-sketch paragraphs of those two lemmas (docstrings only) |

## Status of the targets

| target | status |
|---|---|
| `composeP_efficient` | **proved** (axioms `propext`, `Classical.choice`, `Quot.sound`) |
| `composeV_efficient` | **proved** (same axioms) |
| `hbcSecure_compose` | **proved** (same axioms) |

`polyTime_compose` (proved at the base from the three) uses only the standard axioms. No statement was
changed; no ℓ-output PRF is built or needed. The sorry census changes from the base exactly by the removal of
the three targets (31 → 28 declarations, 14 → 13 modules).

## Changed files

| file | base | final | content |
|---|---|---|---|
| `SecureComputation/ComposeSecurity.lean` (owned) | 382 | 449 | imports the 15 helpers; `## Contents`; title without "(statement phase)"; `## Main results` status; the three proofs; their `**Proof sketch.**` paragraphs rewritten to describe the delivered proofs (statement prose unchanged) |
| `ComposeSecurity/Machines.lean` | — | 257 | polynomial-time machines on encoded histories (checkpoint 1) |
| `ComposeSecurity/Efficiency.lean` | — | 575 | the composed parties as polynomial-time functions of the layout (checkpoint 1) |
| `ComposeSecurity/Probability.lean` | — | 124 | the statistical switch, fixing coordinates, negligible × polynomial |
| `ComposeSecurity/Reductions.lean` | — | 106 | advice-dependent pre-/post-processing with extra coins |
| `ComposeSecurity/Assembly.lean` | — | 284 | the assembled view `asmView` and its word form |
| `ComposeSecurity/Runs.lean` | — | 604 | the coins run by run, `GoodRuns`, the real samples under `GoodRuns` |
| `ComposeSecurity/Bounds.lean` | — | 96 | lengths of encodings, transcripts, machine outputs |
| `ComposeSecurity/Sim.lean` | — | 249 | `Φ` (`phiV`, `phiD`), the simulator, the reduction to the hybrid model |
| `ComposeSecurity/Accept.lean` | — | 192 | coin splittings, acceptance with pre-/post-processing, test machines |
| `ComposeSecurity/Correct.lean` | — | 204 | correctness of a secure protocol, the union bound over the runs |
| `ComposeSecurity/Chain.lean` | — | 260 | the hybrid argument over the runs (generic) |
| `ComposeSecurity/Template.lean` | — | 183 | the reduction of one hybrid step with the worst-case template as advice |
| `ComposeSecurity/Lengths.lean` | — | 286 | polynomial bounds on the words of the templates |
| `ComposeSecurity/SideA.lean` | — | 453 | Alice's side (`exists_simA`) |
| `ComposeSecurity/SideB.lean` | — | 438 | Bob's side (`exists_simB`) |

Sketch edits: `composeP_efficient`, `composeV_efficient` (checkpoint 1) and `hbcSecure_compose` (final) have
sketches describing the delivered proofs. The docstring of `polyTime_compose` still says "`sorry`s under their
sketches" about the efficiency theorems: it is another declaration's statement prose, which the brief freezes, so
I left it and flag it for the landing edit.

## The proof of `hbcSecure_compose`

Polynomial time is `polyTime_compose`. For each side there is one simulator, and for a distinguisher `D` the sum of
the two sides' negligible bounds bounds both advantages (each bound dominates a distinguishing advantage, so it
is nonnegative). Alice's side (`exists_simA`; Bob's, `exists_simB`, is symmetric, with `ρ.V`'s coins, Alice's moves
read and the leading fillers):

1. **Simulator** (`ComposeSim.exists_simulator`): `S_A^H` post-processed by `Φ = phiV`, which recomputes the call
   inputs from the `main`-tape of the simulated `main`-view, runs `S_A^ρ` on each with its answer block and a fresh
   coin block, and assembles the view (`asmView`). Coins `S_A^H.coins + calls · S_A^ρ.coins`.
2. **Output clause and switch** (`exists_correct`, `uprob_not_goodRuns_le`, `distAdv_le_uprob_of_eq`,
   `realA_compose_sampleA`): with the worst-case inputs of each length as advice of a test machine, every party's
   `ρ`-output is wrong with probability `≤ ε_c(n)`; off `¬GoodRuns` (probability `≤ L(n) ε_c(n)`) the real sample is
   `sampleA m (real run views)` on the coins `composeCoins (m, t)`.
3. **Hybrids over the runs** (`ComposeProb.abs_chain_le`, `exists_hyb_step`, `exists_gapA`, `exists_gap_le`): hybrid
   `i` has runs `< i` simulated. Overwriting run `i`'s seeds (`acceptProb_update`) and fixing the other
   coordinates at their worst value (`exists_abs_sub_le_sections`) reduces a step to one `ρ`-sample: the reduction
   `D ∘ hybW` holds as advice the template of the worst instance `(x, y, i, coordinates)` of length `n` (header,
   the other runs' words, Bob's output; polynomially long by `exists_tmplA_bound`), inserts the sample's view and
   assembles. Each step is `≤ ε₂(n)`, the chain `≤ L(n) ε₂(n)`.
4. **Hybrid model** (`acceptProb_realA_dPhi`, `ComposeProb.acceptProb_post_pre`, `exists_dPhi`): with all runs
   simulated the sample is `D ∘ Φ` on `H.realA F n x y` (the extra coins read as blocks, `blocksCoins`), and `D` on
   `S_A` is `D ∘ Φ` on `F.idealA S_A^H`; `H.HBCSecure F` gives `ε₃(n)`.
5. **Total** `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)` (the brief's `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)` with
   `ε_c = ε_A + ε_B`), negligible by `negligible_polyExpr_mul` and `Negligible.add`.

Edge cases: `L(n) = 0` (no hybrid step; the instance type of `exists_gap_le` is empty at such `n`, where the advice
is `[]`; the union bound is `0`); `ρ.rounds(n) = 0` (empty run chunks); `hM` (in `realA_compose_eq`,
`realB_compose_eq`); the fillers and the leading fillers (`segW`, `asmView`); the tape cut lengths (exact on real
views: `padTo_of_length`); `padFin` readback (`answersRealA_eq_answersA`); Bob's side (`SideB.lean`, symmetric).

## New declarations

Checkpoints 1 and 2: as listed in their reports (unchanged since, except the reuse commit `5b90f0dac`, which
removed `acceptProb_seed_fst`, `uprob_fst_eq`, `uexp_le_of_le`, `uprob_coord`, `distAdv_triangle`). Final:

- `Chain.lean` (`ComposeProb`): `hybV` (+`hybV_eq`), `plugV` (+`plugV_eq`), `hybV_update`, `hybV_succ_update`,
  `exists_hyb_step`, `acceptProb_hyb_zero`, `acceptProb_hyb_last`, `abs_chain_le`, `getD_plug`.
- `Template.lean` (`ComposeSim`): `tmplW` (+`tmplW_eq`), `hybW` (+`hybW_eq`), `hybW_tmplW`, `polyTimeComputable_hybW`,
  `exists_gap_le`.
- `Lengths.lean`: `HybridProtocol.length_answersA`, `length_answersB`, `exists_main_msgs_le`,
  `exists_main_outV_le`, `exists_main_outP_le`; `ComposeBound.exists_viewP_le`, `exists_viewV_le`,
  `exists_runAt_le`; one private `exists_ofFn_eq` (see Overlap).
- `SideA.lean` (`HybridProtocol`): `viewRunA` (+`_eq`), `simRunA` (+`_eq`), `sampleA` (+`_eq`),
  `realA_compose_sampleA`, `exists_tmplA_bound`, `exists_gapA`, `acceptProb_realA_dPhi`, `exists_simA`.
- `SideB.lean` (`HybridProtocol`): the same with `B`.

Every new public `def` has its `_eq` reader; every new declaration has a docstring with its formula; every proof of
15 lines or more has a `**Proof sketch.**` paragraph; no `@[simp]`.

## Overlap and reuse

Searches: `evidence/overlap/dupsearch-base.log` (checkpoint 1), `dupsearch-base-cp2.log` (every new name and
statement shape, on a checkout of the base), `dupsearch-final.log` (the same patterns on the final tree), and a
scan of the published lemma lists of the modules in the permitted import closure. The checkpoint-2 overlap table
(in its report, repeated here in short) and the checkpoint-1 table stand; additions for the final helpers:

Reused (final): `acceptProb_fst`, `acceptProb_snd`, `acceptProb_update` (`Pseudorandom/Indistinguishability.lean:73,83,103`),
`abs_sub_le_sum_hybrids` (`Foundations/Probability.lean:218`), `acceptProb_comp_equiv`, `Finset.exists_max_image`,
`NUPPT.runAtL_eq_output_layout`, `coinBlock_flatten`, `Protocol.transcript_eq_transcriptWith`, `View.encode_mk`,
`length_pairEncode`, `PolyExpr.eval_*`.

| new declaration | nearest relative | relation, and why not reused |
|---|---|---|
| `hybV`, `plugV`, `exists_hyb_step`, `acceptProb_hyb_zero/last`, `abs_chain_le` | `Pseudorandom/Indistinguishability.lean:198–330` `multicopyHybrid`, `multicopyRed`, `acceptProb_multicopyRed_left/right`, `exists_multicopyRed_ge` | the same hybrid argument for `t` i.i.d. copies of one sampler; here the runs share the seed `m` and run `j`'s samplers depend on `m` and `j`, so the multicopy statements do not apply. The resampling step reuses `acceptProb_update` (as `acceptProb_multicopyRed_left` does). New. |
| `getD_plug` | `ZeroKnowledge/CommitmentLemmas.lean:189` (`ofFn (update W k z)` split at `k`) | the list form of plugging one entry; not importable. New. |
| `tmplW`, `hybW`, `exists_gap_le` | the worst-case-advice reductions written inline with `Finset.exists_max_image` (`Encryption/PublicKey/Hybrid.lean:295`, `Pseudorandom/NextBit.lean:411`, `ZeroKnowledge/Commitment.lean:317`) | no published lemma packages "argmax instance as advice"; new, generic in the samplers and the instance family. |
| `length_answersA`, `length_answersB` | owned file `length_answersRealA`, `length_answersRealB` (`ComposeSecurity.lean:128,135` final; 88, 95 at the base) | the same computation for `answersA`/`answersB` (Hybrid.lean) instead of the honest answers; the owned file's are about other definitions. New. |
| private `exists_ofFn_eq` (`Lengths.lean`) | owned file's private `exists_ofFn_eq` (`ComposeSecurity.lean:122` final; 82 at the base) | **restated** (two lines from `List.ofFn_getElem`): the owned file's declarations are foreign to the helpers and it is private there. Disclosed here. |
| `exists_main_msgs_le`, `exists_main_outV_le`, `exists_main_outP_le`, `exists_viewP_le`, `exists_viewV_le`, `exists_runAt_le` | owned `compose_msg_bound` (the message half); `InteractiveProofs.lean:133` (`ProverBounded` clauses) | the polynomial bounds the advice needs, built from `H.PolyTime`, `G.PolyTime ρ`, `Efficient.length_next_le`, `length_runAt_le`. New. |
| `viewRunA/B`, `simRunA/B`, `sampleA/B` and the side lemmas | `realViewA/B` (`Runs.lean`), `phiV_view` (`Sim.lean`) | the per-run words and the sample as functions of the coordinates. New. |

## Scope requests

None.

## Promotion requests

As in the checkpoint reports (the FP/history toolkit of `Machines.lean`, `Efficient.exists_polyTime`,
`polyTimeComputable_slots`, `negligible_polyExpr_mul`, the coin splittings, the acceptance lemmas). In addition:
`abs_chain_le`/`exists_hyb_step` (a hybrid argument over non-identical, seed-sharing coordinates) beside the
multicopy lemma in `Pseudorandom/Indistinguishability.lean`, and `exists_gap_le`'s argmax-advice pattern as a
generic lemma for the asymptotic layer.

## Checks

- **Order** (`evidence/final/order-final.txt`, `reorder.log`): `order.txt` with the 15 helpers inserted before their
  consumers (167 modules).
- **Sweep** (`evidence/final/`): **167/167 exit 0, 0 error diagnostics** (`sweep-errors.txt`, counted with
  `^\S+\.lean:\d+:\d+: error[:(]`; `sweep.tsv`, logs `sweep/`). History in `sweep-run.log`: full sweep at
  `756cb2c88`; after the seal fixes the rows from `Probability` (position 140) to the end were moved to
  `sweep-superseded.tsv` (logs `sweep-superseded/`) and re-checked at `034f90a97`; after the docstring commit the rows
  from `Lengths` (position 160) on were moved again (logs `sweep-superseded2/`) and re-checked at `d3f405d46`. Rows
  1–139 are modules none of the later commits touch; every row's module is identical at `d3f405d46`.
- **Sorry census** (`evidence/final/sorry-census-final.txt`, `census-diff.txt`): 28 declarations in 13 modules; the
  only change from the base census (31 in 14) is the removal of `composeP_efficient`, `composeV_efficient` and
  `hbcSecure_compose`.
- **Axioms** (`evidence/axioms/axioms-final.log`): all **258** stored constants of the owned file and the 15 helpers
  use only `propext`, `Classical.choice`, `Quot.sound`; the three targets and `polyTime_compose`:
  `[Classical.choice, Quot.sound, propext]`.
- **Rule 10 — seals** (`evidence/seals/`, tool `seals.py`, sources `evidence/scratch-src/seal/`): whole-file seals of
  the owned file at the base (ROOT = base checkout) and of the owned file and the 15 helpers at the final tree,
  each over its full TCSlib import closure (every module of the closure foreign), in the four variants strict-A,
  strict-B, coe-A, coe-B (A: `PolyExpr.eval` exempt as notation; B: sealed; strict: projection coercions sealed;
  coe: the `FinDist` coercion exempt). Errors counted with `^\S+\.lean:\d+:\d+: error[:(]`, raw logs kept.
  - base: 4/4 exit 0, **0 errors** (670/671/669/670 requests).
  - final: **64/64 exit 0, 0 errors** (`final/results.jsonl`; e.g. the owned file 1192/1193/1191/1192 requests).
    The first final run found failures, all fixed by the two Rule-10 commits and re-sealed; the superseded results
    are kept (`final/results-superseded.jsonl`, logs `final/superseded*/`): `Lengths` `exists_main_msgs_le`,
    `exists_viewP_le`, `exists_viewV_le` (transcript read as `transcriptWith`; then simp normal forms that differ
    under the seals), `Probability` `acceptProb_eq_uexp_sections` (`acceptProb` by `rfl`), `SideA` `exists_simA`,
    `SideB` `exists_simB` (`distAdv` by defeq); each failed in all four variants alike.
  - strict vs coe: the variants differ by one request (the `FinDist` coercion instance, which is in the closure);
    no result differs between them.
- **Paired controls** (`evidence/controls/`, source `evidence/scratch-src/controls/Controls.lean`, tool
  `controls2.py`): seven pairs (`segW`, `tmplW`, `inA`, `hybV`, `viewRunA` of my helpers; `answersA` of the frozen
  `Hybrid.lean`; `PolyExpr.eval`). Unsealed every example closes; in each sealed variant each `CONTROL` fails exactly
  once and each `READER` closes; the `PolyExpr.eval` control fails exactly in the B variants (`results.json`).
- **Explicit-unfold scan** (`evidence/rwids/`, tools `rwids.py`, `rwids_run.py`): every identifier given to
  `rw`/`simp`/`unfold`/… in the 16 files resolves to a theorem, a local hypothesis, or one of the file's own
  definitions (`phiD`, `simV` in `Sim.lean`); no foreign definition is unfolded by name.
- **Statement check** (`evidence/headers/headers-final.txt`): 11 → 11 base declarations, headers, `omit … in` lines
  and statement prose byte-identical: **0 differences**; control (`control-final.txt`): one altered character →
  exactly one difference.
- **Width and size** (`evidence/checks/widths-final.txt`): no line over 100 characters; every file ≤ 1000 lines.
- **Sketches** (`evidence/checks/sketches-final.txt`): every proof of 15 lines or more has a `**Proof sketch.**`
  paragraph; the one flag is the definition `runW` (a body, not a proof).
- **Lint** (`evidence/lint/lint-final.txt`, `lintdiff-final.txt`): 92 FAIL / 101 WARN, line sets equal to the base's
  (`lint-base.txt`): **no new FAIL, no new WARN, none gone**.
- **Environment.** As at checkpoint 1 (`evidence/logs/`): packages symlinked at the manifest's pins (11 match, 0
  mismatch, 4 absent), narrowed cache get (74 roots), bootstrap 152/152. One Lean process at a time against the
  olean tree; no `lake build`. The host restarted several times during the work (uptime resets); the resumable
  runners re-checked any module or probe that had started without finishing, as recorded in the run logs.
  Development checks of single files used a scratch copy compiled with `lean` and a heartbeat limit (not evidence).
  The repository's `AGENTS.md` asks agents to read goals from the VS Code infoview rather than run Lean from a
  shell; this environment has no editor, and the brief prescribes `scripts/lean_check_tree.sh`, so every check went
  through that script (one module per call) or the scratch copies above; `lake build` was never run.

## Patches and reproduction

`patches/0001…0012-*.patch` and `patches/COMMITS.tsv`; a scratch clone at the issue base applies the series with
`git am`, the committer of each row set from `COMMITS.tsv`, and reproduces every hash and the final tree
(`evidence/amcheck/amcheck-final.log`).

## Evidence

`evidence/SHA256SUMS` covers every evidence file (inputs, raw logs, `results.jsonl`, seal/control/scan/axiom sources,
tools); the top-level `SHA256SUMS` covers every delivered file except itself; both checked against the delivered
paths.
