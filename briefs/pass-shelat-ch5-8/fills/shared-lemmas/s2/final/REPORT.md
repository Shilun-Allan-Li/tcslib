# Fill `reject-blocks-s2` — REPORT

**Status: FINAL (complete).** H15 `polyTimeComputable_rejectBlocksL` is proved with its frozen
header; all four consumers (dl-a `DiscreteLog.lean`, dl-c `ElGamal.lean`, the RSA unit sampler,
the Rabin odd/Blum generators) consume it; every copied loop is deleted (64 private declarations)
and all six public sketches are refreshed. Owned `sorry` 1 → 0, `TCSlib/` 511 → 510; no new
`admit`/`axiom`/`sorryAx`. All 422 Checks prerequisites and `audits/pass-shelat/Checks` pass on
this host; the Checks axiom prints equal the base multiset; whole-file import-closure seals fail
only at the five Gate 08 example declarations, identically at the ancestor. No escalation.

## Identity

| item | value |
|---|---|
| frozen source ancestor | `31348fcf7dee32f84db1fc8f929d80653137995e` (exact; `git rev-parse HEAD` after checkout) |
| fill branch | local `fill/reject-blocks-s2`, never rebased, never pushed |
| checkpoint 2 head | `144c99ea` — "S2 milestone 2: prove polyTimeComputable_rejectBlocksL (H15) via the repetition host" (exchange `ae2be1b7`) |
| checkpoint 3 head | `5a6f8021` — "S2 milestone 3: dl-a and dl-c consume H15; retire dla_ss*/dlc_ss* loops; refresh three sketches" (exchange `6fc5aca0`) |
| checkpoint 4 head | `538b932d` — "S2 milestone 4: RSA unit sampler and Rabin generators consume H15; retire rsa_us*/rabin_rb* loops; refresh three sketches" (exchange `9b27244a`) |
| **final head** | `125a2963` — "S2 final: proof sketch for rsa_unitAcc_poly (style-lint finding)" (docstring only) |
| patch series | 4 commits `144c99ea`, `5a6f8021`, `538b932d`, `125a2963` from the ancestor (`patches/`); `src/` = the five files at the final head |
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

## Milestone 5: final checks

### Prerequisites and Checks (`evidence/logs/prereq-build.log`, `prereq-build-2.log`)

* The 328 Checks prerequisites outside `inputs/order.txt` were built in `inputs/checks-order.txt`
  order, one `scripts/lean_check_tree.sh` invocation per module through `tools/chkS.py` (start/end,
  rc, peak RSS of the child tree, fresh nonempty object required). None of them imports an owned
  module (checked from the source imports), so they are independent of the fill.
* Driver history (disclosed): the first driver (`tools/s2_prereq.sh`) built modules 1–51. I then
  found the style-lint finding below and edited a docstring in `RSA.lean`; to keep the objects
  consistent I stopped that driver's shell between modules (its in-flight module, `CookLevin/Hardness`,
  ran to completion: rc 0, 319.9 s). The second driver (`tools/s2_prereq2.sh`) waited for that Lean
  process to exit, skipped the 51 modules whose objects were newer than the first driver's start,
  built the remaining 277, rechecked the eight owned/downstream modules of `inputs/order.txt`
  against the edited RSA (all rc 0), then checked `audits/pass-shelat/Checks`.
* Totals: 337 checks (328 prerequisites, 8 owned/downstream, Checks), every rc 0 with a fresh
  object; peak RSS 3599 MiB (Checks); 4037 s summed wall time; slowest `ClassP/BinaryArith/DetMod`
  1418 s. Never more than one Lean process; no check ran against a missing prerequisite.
* **`audits/pass-shelat/Checks`: rc 0, 137.2 s, 3599 MiB, fresh object, no errors**
  (`checks-final-Checks.full.log`).

### Public surface (`tools/blocks.py`, `logs/blocks-final.json`)

Declaration blocks of the five files at the ancestor and the final head, compared with comments
and docstrings stripped:

* **Public source-header diff: empty** over all five files (every retained public declaration has
  the same modifiers and header text up to its `:=`); no public declaration added or deleted;
  **no public non-theorem body changed**. The H15 header is byte-identical to
  `inputs/host-header.source.txt` at both the ancestor and the head, followed by ` := by`.
* No `@[simp]`, attribute, `irreducible`, `opaque`, `axiom`, `implemented_by`, `unsafe`,
  `set_option`, `import`, `open`, `namespace`, `section` or `variable` line was added or removed
  (scan of the diff).
* Changed declarations (code, not only docstrings): public theorems
  `polyTimeComputable_rejectBlocksL` (proof), `polyTimeComputable_expSampleRaw`,
  `polyTimeComputable_oddGenRaw`, `polyTimeComputable_blumGenRaw` (proofs); private
  `dlc_numPoly_sample`, `rsa_ptc_unitSampleStr` (proofs only, headers unchanged), and Rabin's
  `rabin_spOut` (body), `rabin_spOut_eq`, `rabin_spOut_poly`, `rabin_genCore_poly` (headers and
  proofs), `rabin_genCore_eq` (proof); old/new semantics in the milestone-4 section.
  `rabin_gU_eq` moved above `rabin_genCore_poly` unchanged. Public theorems with docstring-only
  changes: `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw`,
  `polyTimeComputable_unitSampleStr`.
* Deleted: 64 private declarations (DiscreteLog 15, ElGamal 15, RSA 18, Rabin 16, listed in the
  milestone sections and `logs/decl-diff-final.md`). Added: 23 private declarations (Concrete 15,
  DiscreteLog 3, ElGamal 2, RSA 3).

### Census (`tools/census.py`, `logs/census-final.json`)

Ancestor `TCSlib/` 511 `sorry`, 0 `admit`, 0 `axiom`, 1 `sorryAx` token; final 510 / 0 / 0 / 1.
The only per-file delta is `Concrete.lean` 1 → 0 (H15's `sorry`); owned files 0 in every
category. The one `sorryAx` token is outside the owned files and unchanged.

### Axioms

* H15, every new private helper and every changed/re-pointed retained declaration, including
  generated auxiliaries (`logs/axioms-touched.txt`, 57 records from `probes/S2Collect.lean`):
  only subsets of `[propext, Classical.choice, Quot.sound]` (20 with all three, 20
  `[propext, Quot.sound]`, 3 `[propext]`, 14 none). `polyTimeComputable_rejectBlocksL`,
  `polyTimeComputable_expSampleRaw`, `polyTimeComputable_egGenRaw`, `polyTimeComputable_egEncRaw`,
  `polyTimeComputable_unitSampleStr`, `polyTimeComputable_oddGenRaw`,
  `polyTimeComputable_blumGenRaw`: `[propext, Classical.choice, Quot.sound]`.
* Whole-module walk at checkpoint 4 (`logs/axioms-m4.log`): 1280 declarations of the five
  modules, none on `sorryAx`.
* **Aggregate comparison** (`tools/axcmp.py`, `logs/axioms-checks-compare.json`): final Checks
  prints vs the base Checks log (the Gate 08 round-2 native log of S1 head `84f35910`, whose
  library is identical to this ancestor per the pre-ship source identity; I did not rerun Checks
  at the ancestor). Base: **367 records, 364 distinct names; 364 dependency-bearing records over
  361 distinct names; 4 `sorryAx` records**. Final: identical counts, and the two 367-record
  multisets are equal (duplicates included). The four `sorryAx` records
  (`decides_of_decidesWithAdviceInTime`, `lemma_64_3`, `theorem_63_1`, `exists_canonizerExp`) are
  unchanged base debt; H15 had no Checks-printed consumer at the base, so no Checks record changes.

### Rule 10: seals and controls (`tools/s2_seal.py`, `logs/seal-summary.json`, `seals/`)

* **Collection** (`probes/S2Collect.lean`, adapted from the Gate 08 round-2 `CollectExpanded` /
  `CollectConservative` collectors, same exclusions: instances, reducible non-matchers,
  `Complexity.PolyExpr.eval`, `TCSlib.Cryptography.glNeed`). Conservative import-closure lists
  (closures from source imports, identical to Gate 08's): Concrete 830, DiscreteLog 1236,
  ElGamal 1335, RSA 984, Rabin 1060 = **5445 pairs**. They differ from Gate 08's lists only by the
  moved private helpers of imported owned modules (e.g. Concrete's `rbl_*` and the repetition
  matcher's splitter now appear in the downstream lists; the deleted `dla_ss*`/`rsa_us*` are
  gone). Elaborated reads (types and values of every constant of each module, private and
  generated helpers and matchers included, transitively through the module's own definitions):
  every foreign ordinary definition read lies in the conservative list, except
  `Complexity.PolyExpr.eval`, a documented exclusion (read through its `eval_*` lemmas).
* **Whole-file seals**, head and ancestor: a probe copy of each whole file with its list inserted
  after its `namespace`/`open` lines by a `run_cmd` that resolves every printed name against the
  environment (numerical/hygienic private names included), installs
  `attribute [local irreducible]`, verifies the installed status, and counts already-irreducible
  names separately; seal-command diagnostics are rejected as harness failures (none occurred; no
  unsafe reducibility override). The ancestor copies are elaborated in the same imported
  environment as the head copies (same public surface; the imported owned modules' private
  helpers are not referable from another file), with the same lists. Results (active / already
  irreducible / error diagnostics / failing declarations), **identical at head and ancestor**:

  | file | active | already | errors | failing declarations |
  |---|---|---|---|---|
  | Concrete | 830 | 0 | 1 | `primesPairEquiv_apply_val` |
  | DiscreteLog | 1218 | 18 | 3 | `ExpGroupGen.FullLength.exists_fullLengthExcept` |
  | ElGamal | 1317 | 18 | 0 | — (rc 0) |
  | RSA | 984 | 0 | 1 | `rsaTrapdoor_oneWay` |
  | Rabin | 1060 | 0 | 2 | `rabinCollection_index`, `rabinBlumTrapdoor_index` |

  These are exactly Gate 08's five-owned-file examples; all are untouched with code identical to
  the ancestor; **no new or touched declaration fails** (H15 and its `rbl_*` helpers, including
  `rbl_loop_poly` which reads the sealed repetition matcher only through `split`; the re-pointed
  consumers). Base seals **were rerun** here (the `Anc` rows), against the issue ancestor.
* **Controls.** Standalone anonymous-read control (an `example` whose only foreign read is
  `primeStr` by `rfl`): unsealed rc 0; sealed rc 1, one error at the `rfl` (3:135); repeated under
  the complete head RSA import-closure seal: unsealed rc 0, sealed rc 1, one error at the proof
  (28:135). Repetition-matcher control (pre-ship `MatcherUnsealed`/`MatcherSealed` sources
  verbatim): unsealed rc 0; sealed rc 1, one error at the proof (7:52). `primeStr` is in the RSA
  list and `polyTimeComputable_iterateFind.match_1` in the Concrete list.
* **Explicit unfold scan** (`tools/unfoldscan.py`, `logs/unfoldscan.json`,
  `logs/unfoldscan-kinds.json`): all 92 `simp`/`simp only`/`simpa`/`dsimp`/`rw`/`rwa`/`erw`/
  `unfold`/`delta`/... occurrences in the 37 new/touched declarations, bracketed lists read across
  blank and comment-only continuation lines; the 121 distinct identifiers were resolved in each
  file's namespace and `open` scope by the probe. Non-theorems among them: only own-file
  definitions (`dlW`, `expSampleRaw` in DiscreteLog; `rabinGenRaw`, `rabinGenOut`,
  `rabinGenParams`, `rabinIndexOf`, `samplePrimePL` in Rabin); the unresolved ones are local
  hypotheses, `show … from` terms and own-file private names. **No foreign TCSlib definition
  and no core/Mathlib definition is passed to `simp`/`rw`/`unfold`/`dsimp`/`delta`.** Core and
  Mathlib definitions reduce only in `rfl`/`show`/`decide` steps or elaboration-time defeq.
  Foreign definitions mentioned by the touched declarations' types/terms are listed in
  `logs/touched-foreign-mentions.txt`; the seals show none is read definitionally.

### Lints (`logs/style-lint-*.log`, `logs/campaign-lint*-*.log`)

* `scripts/style_lint.py` on the five files: ancestor 4 findings, final 4 findings, the same four
  pre-existing size findings (DiscreteLog, ElGamal, RSA, Rabin over 1000 lines; all four shrank).
  At checkpoint 4 a fifth finding appeared (`rsa_unitAcc_poly`, 24-line proof without a
  **Proof sketch.**); fixed at the final head by a docstring sketch. Exit 1 at both ancestor and
  head because of the accepted size findings — not a clean exit.
* `scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates`, plain and `--check8b`: 0 FAIL,
  12 WARN at both; the only differences are line and private-declaration counts. No new public
  definition, so check 8b is unchanged and no E-API is needed.

## Sizes

| file | ancestor | final |
|---|---|---|
| Concrete | 751 | 935 (+184, under 1000) |
| DiscreteLog | 1348 | 1194 (−154) |
| ElGamal | 2269 | 2134 (−135) |
| RSA | 2610 | 2417 (−193) |
| Rabin | 3678 | 3553 (−125) |

(`wc -l`; the lints count one more line where the file lacks a final newline.) Net 469
insertions, 892 deletions. Size exceptions: the four files above 1000 lines were already above it
at the ancestor (approved fill-owned size findings); this fill reduces each.

## Six sketch dispositions

| public theorem | disposition |
|---|---|
| `polyTimeComputable_expSampleRaw` | refreshed (H15 with `v < m`), proof re-pointed |
| `polyTimeComputable_egGenRaw` | refreshed (H15 via `dlc_numPoly_sample`), proof unchanged |
| `polyTimeComputable_egEncRaw` | refreshed (H15 via `dlc_numPoly_sample`), proof unchanged |
| `polyTimeComputable_unitSampleStr` | refreshed (H15 with the unit test), proof via the re-pointed private `rsa_ptc_unitSampleStr` |
| `polyTimeComputable_oddGenRaw` | refreshed (H15 in `rabin_spOut_poly`), proof re-pointed |
| `polyTimeComputable_blumGenRaw` | refreshed (H15 in `rabin_spOut_poly`), proof re-pointed |

Statement prose, formulas and citations are unchanged; only the loop description was replaced.

## Harvest and payback

H15's private loop (`rbl_*`) is the Rabin fill's private block loop (`rabin_rb*`,
`rabin_rbFind_eq`), generalized with the parameter word in the header and the test applied to
`⟨par, trial word⟩`; it is the only harvested code, and its source copy is deleted. Payback: four
private loop families (64 declarations) are replaced by one host instance each; net −423 lines.
The new consumer-side helpers are only the acceptance tests (`dla_belowAcc*`, `dlc_belowAcc*`,
`rsa_unitAcc*`).

## Interface gaps

None needed (no E-API/E-FREEZE/E-TRUE/E-RES). Frictions handled locally: the tail primitive is
stated with `List.drop 1` (transported by `List.drop_one` through `PolyTimeComputable.congr`, as
the pre-ship route did); `PolyTimeComputable.comp'` needs the explicit outer function
`(g := fun x => List.replicate (p.eval x.length) true)` for `polyTimeComputable_unaryPoly`
(otherwise higher-order unification picks `List.cons true`).

## Commands

* Lean: `python3 -I tools/chkS.py <module>` → `bash scripts/lean_check_tree.sh <module>` with
  `TCSLIB_OLEANS=/workspace/s2-oleans`, one module per invocation, one Lean process at a time.
  The repository `AGENTS.md` advises the VS Code LeanInfoView instead of shell builds; the brief
  explicitly authorizes this shell checking method for the campaign, and no LeanInfoView exists on
  this host. No library-wide `lake build`, no unfiltered cache get.
* Python tools in `evidence/tools/` (`census.py`, `blocks.py`, `decl_diff.py`, `unfoldscan.py`,
  `axcmp.py`, `s2_seal.py`, drivers `s2_prereq.sh`, `s2_prereq2.sh`, delivery `s2_deliver.sh`);
  Lean probes in `evidence/probes/` and `evidence/seals/*.source.txt`.

## Honest limits

* The base Checks print set is Gate 08's native log at S1 head `84f35910` (library-identical to the
  ancestor), not a rerun at the ancestor on this host.
* The ancestor seal copies were elaborated against the current objects of their imported owned
  modules (public surface unchanged); the ancestor's own olean tree was not rebuilt.
* The unfold scan is a text scanner over tactic lemma lists with Lean name resolution, not a full
  Lean syntax analysis; seals do not detect explicit unfolds of owned definitions (allowed).
* The bootstrap driver disclosure (milestone 1) and the stopped/resumed prerequisite driver
  (above) are process facts; no check result depends on them.
* Clear to merge only after delivery review and a user-approved PR.

Patch reproduction: `git am` of the four `patches/` at the ancestor in a scratch worktree
reproduces all five `src/` files byte-for-byte (5 files, 469 insertions, 892 deletions).
