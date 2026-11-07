# Fill `reject-blocks-s2` — REPORT

**Status: CHECKPOINT 4 (milestone 4 reached).** H15 is proved (milestone 2); all four consumers
(dl-a `DiscreteLog.lean`, dl-c `ElGamal.lean`, the RSA unit sampler, the Rabin odd/Blum
generators) consume it; every copied loop is deleted and all six public sketches are refreshed.
The final checks (milestone 5) follow.

## Identity

| item | value |
|---|---|
| frozen source ancestor | `31348fcf7dee32f84db1fc8f929d80653137995e` (exact; `git rev-parse HEAD` after checkout) |
| fill branch | local `fill/reject-blocks-s2`, never rebased, never pushed |
| checkpoint 2 head | `144c99ea` — "S2 milestone 2: prove polyTimeComputable_rejectBlocksL (H15) via the repetition host" (exchange `ae2be1b7`) |
| checkpoint 3 head | `5a6f8021` — "S2 milestone 3: dl-a and dl-c consume H15; retire dla_ss*/dlc_ss* loops; refresh three sketches" (exchange `6fc5aca0`) |
| checkpoint 4 head | `538b932d` — "S2 milestone 4: RSA unit sampler and Rabin generators consume H15; retire rsa_us*/rabin_rb* loops; refresh three sketches" |
| exchange read | `exchange/pass-shelat-ch5-8` at `d14a685` (≥ `d38aea96`); pack `SHA256SUMS` verified (all OK) |
| owned baseline | all five fingerprints and line counts equal `inputs/owned-baseline.json` (`evidence/logs/owned-baseline-check.log`) |
| worker | one Claude session, no sub-agents |

## Milestone 1: environment (addendum v1, Part 1)

* Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 with no memory limit, so the
  headroom is `MemAvailable` = 15.42 GiB (floor 4 GiB): PASS; clone filesystem (ext4, `/dev/vda`)
  free 20.47 GiB (floor 12 GiB): PASS. `TMPDIR` unset; nothing on tmpfs.
* Toolchain Lean 4.25.0 (the pin), already installed under elan on this host by earlier fills of
  this session. Lean starts normally; no shim.
* Cache store logged first (`cache-store.log`: it existed, 2366 files, from earlier fills of this
  session on this host). Narrowed fetch for the **144** Checks roots (`inputs/checks-roots.txt`,
  recomputed from `inputs/checks-order.txt` and identical): "Attempting to download 722",
  "Decompressing 3086", "Downloaded: 722 file(s) [attempted 722/722 = 100%]", exit 0
  (`cache-get.log`). Packages present match the manifest; absent `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery`, `MD4Lean` (`packages-check.log`). No zero-length package oleans
  (`zero-oleans.log`). Cache probe importing `Mathlib.Algebra.BigOperators.Field` (first root):
  exit 0 (`cache-probe.log`).
* Candidate bootstrap of `inputs/order.txt` (94 modules) through `scripts/lean_check_tree.sh`, one
  module at a time, into the scratch olean tree `/workspace/s2-oleans` (`bootstrap.log`; wrapper
  `tools/chkS.py` logs start/end/rc/peak RSS and requires a fresh nonempty object). Modules 1–93
  passed, the five **baseline** owned files included (Concrete with H15's `sorry` warning). The
  background driver process ended without logging module 94 (the `TCSlib/Cryptography/Candidates`
  facade, imports only); no Lean process was left running. The facade was then checked in the
  milestone-2 downstream sweep (exit 0). Disclosed; no check was run against missing prerequisites.
* The remaining 328 Checks prerequisites are built before the final `audits/pass-shelat/Checks`
  check (milestone 5).

## Milestone 2: H15

`polyTimeComputable_rejectBlocksL` — header unchanged (statement, hypotheses, `:= by`); the
proof is `exact ⟨g, hg, spec⟩` with private helpers in `Concrete.lean`:

| private | role |
|---|---|
| `rbl_step` | one trial on `⟨⟨⟨bw, kw⟩, par⟩, ⟨counter, coins⟩⟩`: keep the header, drop a counter bit and `|bw|` coins |
| `rbl_block` | the trial word: the first `|kw|` coins |
| `rbl_acc` | counter nonempty and `acc ⟨par, trial word⟩` |
| `rbl_out` | payload `true :: trial word` |
| `rbl_loop` | the repetition host's function, its `match` written as `Option.elim` |
| `rbl_step_poly`, `rbl_block_poly`, `rbl_acc_poly`, `rbl_out_poly` | the pieces are polynomial-time |
| `rbl_step_iterate` | the orbit `⟨h, ⟨c.drop i, s.drop (i·\|bw\|)⟩⟩` (`List.drop_drop`) |
| `rbl_length_step_le`, `rbl_length_step_step_le`, `rbl_length_step_iterate_le` | orbit bound `2n+4` (`StateLoop.length_pairFstD_add_pairSndD_le`) |
| `rbl_loop_poly` | `polyTimeComputable_iterateFind` with `R = var`, `P = 2n+4`; its `match` read by `split` (never by unfolding `polyTimeComputable_iterateFind.match_1`) |
| `rbl_loop_spec` | correctness and the tail bound: `IterateFind.find?_range_and_lt`, `rejectBlocksL_eq_find?`, `List.length_take_le` |

`g z = rbl_loop acc ⟨⟨⟨bw z, kw z⟩, par z⟩, ⟨tw z, c z⟩⟩`. No premise is added: `k = 0`, `B = 0`,
`T = 0`, `k > B`, overlapping blocks and short/empty coins are handled exactly by `rejectBlocksL`
(the counter, not the coins, stops the trials).

**Harvest (disclosed).** Adapted from the Rabin fill's private loop (`rabin_rbStep`,
`rabin_rbBlock`, `rabin_rbAcc`, `rabin_rbOut`, `rabin_rbLoop`, `rabin_rbLoop_poly`,
`rabin_rbStep_iterate`, the length lemmas, `rabin_rbFind_eq`), generalized with the parameter
word in the header and the test applied to `⟨par, trial word⟩`. The Rabin copies are retired at
milestone 4.

**Checks at checkpoint 2** (`evidence/logs/checks-m2.log`): Concrete (4.5 s, 2748 MiB), then the
downstream modules of `inputs/order.txt` in order — Factoring, RSA, Rabin, DiscreteLog,
DiscreteLogHardcore, ElGamal, the facade — all exit 0 with fresh objects.

**Axioms** (`evidence/logs/axioms-m2.log`, `evidence/probes/S2Axioms.lean`):
`polyTimeComputable_rejectBlocksL` depends on `[propext, Classical.choice, Quot.sound]`; every
`rbl_*` helper on a subset; no declaration of the five owned modules depends on `sorryAx`.

**Census** (`tools/census.py`, lexical code tokens excluding nested comments, strings, char
literals and «quoted» names): ancestor `TCSlib/` 511 `sorry` (Concrete 1); checkpoint 2: 510,
owned 0. No `admit`/`axiom` tokens; the one `sorryAx` token is outside the owned files and
unchanged (`census-ancestor.json`, `census-m2.json`).

## Milestone 3: dl-a and dl-c

* **DiscreteLog.** `polyTimeComputable_expSampleRaw` now applies H15 with `E a v := v < a`, the
  parameter word `⟦m⟧ = pairFstD (pairSndD (inArg z))`, width word `sizeStr ⟦m⟧` (`H.size`;
  `length_sizeStr`), block and trial words `inParam z`, coins `inCoins z`, read through
  `sampleBelowL_eq_rejectBlocksL`. The payload's tail (`polyTimeComputable_tail` transported to
  `List.tail` by `List.drop_one` through `.congr`) is width-normalized exactly as before
  (`natToList_zero_append_drop`). Deleted (15): `dla_ssStart`, `dla_ssStep`, `dla_ssBlock`,
  `dla_ssAcc`, `dla_ssOut`, `dla_ssStep_poly`, `dla_ssBlock_poly`, `dla_ssAcc_poly`,
  `dla_ssOut_poly`, `dla_ssStep_iterate`, `dla_length_ssStep_le`, `dla_length_ssStep_ssStep_le`,
  `dla_length_ssStep_iterate_le`, `dla_ssFind_eq`, `dla_ssStart_poly`. Added (3):
  `dla_belowAcc` (the test on `⟨w, b⟩`), `dla_belowAcc_poly` (`H.le_poly`, negated),
  `dla_belowAcc_spec` (`decide (⟦b⟧ < ⟦w⟧)`).
* **ElGamal.** The only loop consumer, `dlc_numPoly_sample`, keeps its statement and is re-proved
  through H15 (same instance shape, parameter word the numeral `m` with `⟦m⟧ = M`, block/trial word
  `u`). Deleted (15): `dlc_ssStep`, `dlc_ssBlock`, `dlc_ssAcc`, `dlc_ssOut`, `dlc_ssLoop`,
  `dlc_ssStep_poly`, `dlc_ssBlock_poly`, `dlc_ssAcc_poly`, `dlc_ssOut_poly`, `dlc_ssStep_iterate`,
  `dlc_length_ssStep_le`, `dlc_length_ssStep_ssStep_le`, `dlc_length_ssStep_iterate_le`,
  `dlc_ssLoop_poly`, `dlc_ssLoop_eq`. Added (2): `dlc_belowAcc`, `dlc_belowAcc_spec` (the
  polynomial-time proof of the test is inlined at its one use). The section docstring of the
  numeral calculus now names H15 instead of the loop.
* **Sketches refreshed** (statement prose, formulas, citations unchanged): `polyTimeComputable_expSampleRaw`,
  `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw`: each now describes the H15
  application (and its empty-on-failure payload) in place of the deleted trial loop.
* Checks (`evidence/logs/checks-m3.log`): Concrete, Factoring, RSA, Rabin, DiscreteLog,
  DiscreteLogHardcore, ElGamal, the facade: all exit 0, fresh objects.

## Milestone 4: RSA and Rabin

* **RSA.** The private `rsa_ptc_unitSampleStr` (the proof behind the public
  `polyTimeComputable_unitSampleStr`; statement unchanged) applies H15 with
  `E a v := v < a ∧ Nat.Coprime v a`, the parameter word `f z` (the modulus numeral `w`), width
  word `sizeStr w` (`H.size`), block and trial words `1^{B(n)}`, `1^{T(n)}`
  (`polyTimeComputable_unaryPoly rsaBlock/rsaTrials`), coins `inCoins z`, read through
  `sampleUnitL_eq` and `length_sizeStr`. The output step (`H.divMod` remainder of the tail or of
  the fallback `[true]`) is as before. Deleted (18): `rsa_usStart`, `rsa_usStep`, `rsa_usBlock`,
  `rsa_usGcd`, `rsa_usAcc`, `rsa_usOut`, `rsa_usLoop`, `rsa_usStep_poly`, `rsa_usBlock_poly`,
  `rsa_usAcc_poly`, `rsa_usOut_poly`, `rsa_usStep_iterate`, `rsa_length_usStep_le`,
  `rsa_length_usStep_usStep_le`, `rsa_length_usStep_iterate_le`, `rsa_usLoop_poly`,
  `rsa_usFind_eq`, `rsa_usStart_poly`. Added (3): `rsa_unitAcc` (the test on `⟨w, b⟩`: not
  `⟦w⟧ ≤ ⟦b⟧`, the `xgcdStr` gcd numeral reads `≤ 1` and `≥ 1`), `rsa_unitAcc_poly`,
  `rsa_unitAcc_spec` (via the retained `rsa_unitTest_eq`). The section header now names H15.
* **Rabin.** Deleted (16): `rabin_rbStep`, `rabin_rbBlock`, `rabin_rbAcc`, `rabin_rbOut`,
  `rabin_rbLoop`, `rabin_rbStep_poly`, `rabin_rbBlock_poly`, `rabin_rbAcc_poly`,
  `rabin_rbOut_poly`, `rabin_rbStep_iterate`, `rabin_length_rbStep_le`,
  `rabin_length_rbStep_rbStep_le`, `rabin_length_rbStep_iterate_le`, `rabin_rbLoop_poly`,
  `rabin_rbFind_eq`, `rabin_spStart`. Changed private adapters (old → new):
  * `rabin_spOut acc0 U ds c` — old: the padded payload of the deleted loop on
    `rabin_spStart U c`, or the padded fallback `ds`; new: `⟦v⟧_{|U|}` where `v` is the value of
    the first of the `4m²` trial words `(c.drop (t·m)).take m` accepted by `acc0` (`List.find?`),
    or `⟦ds⟧`. The two agree whenever `|ds| ≤ |U|` (both are then `⟦(rejectBlocksL …).getD ⟦ds⟧⟧_{|U|}`);
    they can differ only for `|ds| > |U|`, where the old fallback was `rabin_pad U ds` (no
    correctness lemma covered that case). Every use has `|ds| ≤ 3 ≤ |U|`.
  * `rabin_spOut_eq` — the hypothesis `|ds| ≤ |U|` is dropped (now `rejectBlocksL_eq_find?` and
    `hspec`); its two call sites in `rabin_genCore_eq` drop that argument.
  * `rabin_spOut_poly` — now takes `E`, `hspec` and `∀ z, |fds z| ≤ |fU z|`; proof: H15 with
    `E' _ v := E v`, test `acc0 ∘ pairSndD`, parameter word `[]`, width and block word `U`,
    trial word `1^{4m²}`; the result or fallback is padded (`rabin_pad_poly`) and identified by
    `rabin_pad_eq` using H15's tail bound.
  * `rabin_genCore_poly` — now takes `E`, `hspec`, `|ds1| ≤ 3`, `|ds2| ≤ 3` and passes them on
    (bound `3 ≤ max n 3` from `rabin_gU_eq`, which moved above it unchanged).
  * The two public callers pass `(fun v => v.Prime ∧ v ≠ 2)`/`rabin_oddAcc_spec`, resp.
    `(fun v => v.Prime ∧ v % 4 = 3)`/`rabin_blumAcc_spec`, and `(by decide)` lengths; their
    headers are unchanged.
* **Sketches refreshed:** `polyTimeComputable_unitSampleStr` (RSA), `polyTimeComputable_oddGenRaw`,
  `polyTimeComputable_blumGenRaw` (Rabin) now describe the H15 application in place of the loop.
  All six sketches are now refreshed.
* Checks (`evidence/logs/checks-m4.log`): Concrete 4.4 s, Factoring 6.9 s, RSA 19.9 s, Rabin
  12.3 s, DiscreteLog 4.0 s, DiscreteLogHardcore 24.3 s, ElGamal 10.1 s, the facade 2.1 s: all
  exit 0, fresh objects, peak RSS ≤ 3018 MiB; RSA and Rabin elaborate with no warnings.
* Declaration diff vs the ancestor: `evidence/logs/decl-diff-m4.md` (Concrete +15; DiscreteLog
  −15/+3; ElGamal −15/+2; RSA −18/+3; Rabin −16/+0; all private). Census
  (`census-m4.json`): `TCSlib/` 510 `sorry`, owned 0; the sole delta from the ancestor is
  Concrete's H15 `sorry`. Axiom walk (`axioms-m4.log`): 1280 declarations of the five modules,
  none on `sorryAx`; H15 `[propext, Classical.choice, Quot.sound]`.

## Still to do

Milestone 5 (328 remaining prerequisites, `audits/pass-shelat/Checks`, header diff, axiom
comparison with the base, Rule-10 seals with the anonymous-read and repetition-matcher controls,
lints, final sizes).
