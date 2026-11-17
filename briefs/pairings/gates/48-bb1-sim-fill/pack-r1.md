# Gate 48 · the bb1-sim gate: T2 `bb1_sim_real`, T3 `bb1_sim_random` and the `Relational` targets (#357) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This is "the
bb1-sim gate" of the bb1-sim design rulings (Q8), with the scope that Seyoon's DW-11 ruling of 2026-11-17 left it: the
ten reader insertions and the T2/T3 fill. One PR is audited.

- **PR #357** (`bb1-sim` fill): draft [PR #357](https://github.com/Shilun-Allan-Li/tcslib/pull/357) at
  `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff` (branch `land/pairings-bb1-sim`), base `cryptography/pass-shelat-ch2-4` at
  `e1d39836ed4a69a34914c35f4c73c71de853dcc6`, which is also the merge base. Five SSH-signed commits: maintainer-signed
  `git cherry-pick -S` copies of the external worker's four commits (author kept) and the maintainer's landing edit
  LE-bsf1. It changes 9 files (+1925/−21). No stacking: #340 (T1) and #346 (T4) are merged.
- **Records pin:** `e6cdf4d4eed898acd71d48bd60082140eb076cfe`, the tip of `origin/cryptography/pass-shelat-ch2-4` at
  staging. It is the PR base plus one records-only commit (`e6cdf4d4`, "Records: bb1-sim fill phase 2 PASS on snapshot #5;
  draft PR #357", which files `phase2.md`, its evidence ZIP and the review's final verdict). It changes 0 code paths, and
  pin × #357 (tree `b5c1eda7cb5acba4f64383a2da27866187dc64fc`) differs from the pin in exactly the 9 files
  (`checks/series.txt`). Every record this pack cites is read at the pin; this pack's own files are filed after it.
- **Lean base.** The PR base's Lean equals `3f540c22360c869069a0fba684e23ce6f3cb20db`, the merge of #346, whose tree is
  **olean snapshot #5** (Gate 44's adopted T44′ replay; map SHA-256
  `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`, 1458 entries without Mathlib). The diff
  `3f540c22..e1d39836` over `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files and `lean-toolchain` is empty.
- **Scope:** a **proof audit** of four admitted, frozen statements, the ten reader insertions they were granted, the new
  helpers, and the landing edit:

  | Target | File · line at the head | Source |
  |---|---|---|
  | **T2** `bb1_sim_real` | `IB/BonehBoyenSecurity.lean:116` | [BB04, proof of Theorem 4.1], frozen tags |
  | **T3** `bb1_sim_random` | `IB/BonehBoyenSecurity.lean:152` | [BB04, proof of Theorem 4.1], frozen tags |
  | `Games.ProbComp.expect_simulate_rel` | `Games/Relational.lean:85` | [BGZ09], [Sho04] (frozen #351 docstring) |
  | `Games.ProbComp.expect_sample_rel` | `Games/Relational.lean:130` | frozen #351 docstring |
  | consumer `bb1_sidSecure` (frozen whole, unchanged) | `IB/BonehBoyenSecurity.lean:179` | [BB04, Theorem 4.1] at depth 1 |

  T2 and T3 are the last two admissions under `bb1_sidSecure`: T1 (`bdhAssumption_of_dbdhAssumption`, #340) and T4
  (`exists_bb1_distinguisher`, #346) passed Gate 44 (closed on round 2) and are merged. With #357, `bb1_sidSecure`'s
  `sorryAx` trace is empty.
- **Out of scope:**
  - **#351** (the `Games/Relational.lean` statements, the averaging bound in `Games/Probability.lean`, Q1–Q6) and **#352**
    (the `Pairing/Group.lean` helpers, Q10 with LE-grp1) are merged and are **not** audited here. Seyoon ruled on
    2026-11-17 that they go to a later combined gate of small items (**DW-11**; decision-log row "#352 merged"). This
    supersedes the original Q8 wording in `rulings.md`, which put the Games statement phase in this gate. In
    `Relational.lean`, this gate audits only the two bodies; its headers, statement prose, sketches, tags and
    `prob_simulate_rel` are #351's frozen text.
  - **Gate 44** (T1, T4, the seven #346 readers) is closed; **Gate 40** (the statements T1–T4) is closed.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `IB/` is
`AdvancedEncryption/IdentityBased/` and `BBS/` is `IB/BonehBoyenSecurity/`.

## What changed

Lines are base → head (`source-head-r1.json`; every line is at most 100 characters; no tab or trailing space).

| File | Status | What | Lines |
|---|---|---|---:|
| `Games/Relational.lean` | frozen | the bodies of `expect_simulate_rel` and `expect_sample_rel` (+14/−2) | 134 → 146 |
| `IB/Defs.lean` | frozen | six approved readers (pure insertion, +87) | 476 → 563 |
| `IB/BonehBoyen.lean` | frozen | four approved readers (pure insertion, +46) | 714 → 760 |
| `IB/BonehBoyenSecurity.lean` | frozen | five helper imports, a `## Contents` section, T2's and T3's sketches and bodies (+74/−19) | 170 → 225 |
| `BBS/Lazy.lean` | new | the lazy simulator handlers; the scheme-generic `sidSpec_dom_*`/`_rng_*`, `zeroBits_eq_cast` | 447 |
| `BBS/Real.lean` | new | the real game with `h` recorded and drawn late; `RealReads`, `setup_out`, `BB1RealState` and its reader | 423 |
| `BBS/Coupling.lean` | new | step M (design r1 §3.1): `RelM`, the nine `stepM_*` rows, `stepM_call`; the group facts | 565 |
| `BBS/Random.lean` | new | T3's comparison `expect_bb1SimImpl_random` | 139 |
| `BBS/Chain.lean` | new | T2's chain `prob_sidGame_coins` | 130 |

No other path changes; in particular `Games/Probability.lean`, `Games/Hopping.lean`, the `Games` facade, `Pairing/*`,
T4's `IB/BonehBoyenMachine.lean` and `IB/BonehBoyenMachine/*`, the facades and the root are blob-equal at the base and the
head (`git diff --stat` lists exactly the 9 files).

**The proofs** (phase-1 review § *The proofs*; design r1 §3):
- **`expect_simulate_rel`:** induction on the computation `c`, generalizing both states; `simulate_pure`/`_query`,
  `expect_pure`/`_bind`, the per-call hypothesis at a query. **`expect_sample_rel`:** `expect_bind`, then
  `expect_sample_equiv e`, then pointwise `hg` and `hf`.
- **T2** (design §3.1): `setup_out` gives the real setup's outputs; `prob_bind` on both sides and
  `abs_expect_sub_le_expect` with the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]`. On bad coins two probabilities in
  `[0, 1]`; on good coins equality by `prob_sidGame_coins`: `expect_sample_comm`; R1 (`expect_simulate_rel` with `R_h`)
  then E-h (`Games.expect_simulate_eager`); `g₂ = g^{b'}` along `Equiv.ofBijective _ (pow_val_bijective_of_ne_one _ g.2)`;
  step M (`expect_simulate_rel` with `RelM`, whose per-call hypothesis `stepM_call` has nine rows proved by
  `expect_sample_rel` along `e ID`, along `Equiv.addRight (b'/(ID − ID*))` — [BB04]'s `r = r̃ + b/(I − I*)` — and along
  `Equiv.refl`); E-c (`Games.expect_simulate_eager`); `Bridge.expect_sample_pair` twice and `expect_const`. Identity
  injectivity on good coins: `2^{idLen} ≤ p` and `bitsToNat u < 2^ℓ ≤ p`, by Mathlib's `CharP.natCast_injOn_Iio`
  (BS-F01). Finally `prob_eq_expect` and `prob_sample_eq_uprob` give the frozen bound
  `uprob (fun r => (G.inst κ r).order < 2 ^ ℓ.eval κ)`.
- **T3** (design §3.2): unfold both games, swap `T` with `ρ` (`expect_sample_comm`), then `expect_bb1SimImpl_random`:
  E-T on both sides (`expect_simulate_bb1SimLazy`, `zt T = (Z, T)`), then `expect_simulate_congr` with
  `bb1SimLazy_random_call`; at the first valid `Challenge`, `expect_sample_rel` with `R := Eq` along
  `T ↦ decodeT(M₁)⁻¹ decodeT(M₀) T`; every other call is bit-independent (`bb1SimImpl_two_of_not`).
- Every `expect_simulate_rel` and `expect_simulate_eager` use is a single application with handler-specific hypotheses:
  no new eager or relational lemma (DL-33). The only hypotheses carried into T2 are `ho` (from `setup_out`), `hp : 2^ℓ ≤ p`
  (the good-coin event), `hg : g ≠ 1` (from the subtype) and `he` (from `exists_equiv_mul_pow`).

**The ten readers** (Seyoon's Q7 follow-up ruling, 2026-11-17: verbatim pure insertions in this PR, pinned by the
post-insertion SHA-256s):
- `IB/Defs.lean`, after base line 430 (the last line of `oracleImpl_two_onSpec`): `IBEScheme.sidImpl_zero_onSpec`,
  `sidImpl_two_onSpec`, `sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec`,
  `sidImpl_challenge_fresh_onSpec`; block `Defs-block.lean.txt` (86 lines,
  `d6f8faf16bd8b121fbccba9541225ca9761a2ee90b4eda3bf12dead62eaaa239`); head pin
  **`97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0`** (563 lines).
- `IB/BonehBoyen.lean`, after base line 412 (the last line of `bb1Scheme_msgSpace_iff`): `bb1Scheme_setup_eq`,
  `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT`; block `BonehBoyen-block.lean.txt` (45 lines,
  `967f2a303484228d42be74c446cf4a8c2a92fb46ad705ec1a60f24b54427f226`); head pin
  **`88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26`** (760 lines).
- The blocks are byte-identical to the statement job's `READERS-TO-INSERT.md` §2 (exchange `8899115b`, `a3cb45f6`) and are
  in `records/…/issued-fill-r1/readers/`. Base hashes `4e220ead…`/`da875140…` (= T4's head, whose two files the
  readers were written against). The pins are reproduced from git objects in `checks/pins.txt`.

**LE-bsf1** (`7a98ba01`, maintainer, ruling Q2 of 2026-11-17; `Lazy`, `Real`, `Coupling`, +49/−23), byte-identical to the
phase-1 review's `le-bsf1-proposed.diff`:
- adds `BB1Sim.bb1RealState_eq … := rfl`, the reader of the public `abbrev BB1RealState` (`BBS/Real.lean:165`; policy
  §1: a new public `abbrev` lands with its `_eq` lemma) — closes BSF-F02 (checkpoint C1-F03);
- adds "Glue: …" notes to the 21 helper docstrings that had neither a `[BB04, …]` tag nor a glue note, the formulas of
  `bb1SimLazy_eq` and `BB1RealState`, and "a variant of the game of [BB04, §2.1]" for `bb1RealAt`/`bb1RealLazy` — closes
  BSF-F03 (C1-F04). The diff adds 22 lines containing "Glue:" (the 21 and the new reader's own docstring).

**Commits** (`checks/series.txt`, `phase2/landing/`; each carries a `gpgsig`; phase 2 read the ed25519 key
`SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc` from each signature blob, the same key as the records commits):

| Commit | Worker original | What | Files |
|---|---|---|---|
| `69fa787f` | `23614c0a` | the ten readers | `Defs` (+87), `BonehBoyen` (+46) |
| `2845f100` | `3f430cae` | the `Relational` bodies | `Relational` (+14/−2) |
| `469375fa` | `622f5b03` | the five helper modules | `BBS/*` (new) |
| `40f7da54` | `c35595ae` | T2, T3, imports, `## Contents` | `BonehBoyenSecurity` (+74/−19) |
| `7a98ba01` | — | LE-bsf1 (maintainer) | `Lazy`, `Real`, `Coupling` |

The worker's four commits were delivered unsigned as patches (exchange `2467bc3b`, `inbox/fills/bb1-sim/`); `git am` at
the patch base `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c` reproduced their hashes (phase 1 and again in phase 2), and
`git range-diff 72c0498a..c35595ae e1d39836..40f7da54` is 4/4 `=`. At `40f7da54` the 9 files equal `c35595ae`'s byte for
byte; the base differs from the patch base only by #340 (`Pairing/Assumptions.lean`) and LE-g44 (`Draws`, `Words`,
`Handler`), none of them a fill file.

## Rulings and records in force

1. **The bb1-sim design rulings** (`fills/bb1-sim/rulings.md`, 2026-11-16): Q1 a new `Games/Relational.lean`; Q2 the
   names; Q3 the inline-expectation form of the per-call hypothesis; Q5 no query budget; Q7 readers by approved insertion;
   Q8 one bb1-sim gate; Q9 the PR on the tip once T4 merges; Q11 [BGZ09]/[Sho04] are cited in `Relational.lean` (#351),
   and the fill adds no tag for them.
2. **The Q7 follow-up** (Seyoon, 2026-11-17): exactly ten readers, verbatim pure insertions after the anchors, pinned by
   `97ecb6e0…` and `88454d6f…`, `rfl` or one-line proofs, no definition change. **This gate checks that they are
   insertions only.** The design point: the fill reads the real setup through the probe's `RealReads`/`setup_out`.
3. **DW-11** (Seyoon, 2026-11-17): #351 and #352 are audited in a later combined gate, not here.
4. **BS-F01 / LE-grp1** (2026-11-17): `natCast_inj_of_lt` was dropped from `Group.lean`; the fill uses Mathlib's
   `CharP.natCast_injOn_Iio` directly.
5. **The bb1-sim fill rulings** (Seyoon, 2026-11-17): **Q1** accept the `sidSpec_*` overlap with T4's private twins as
   **DL-57**, repaid in cleanup Stage 2; **Q2** LE-bsf1 as drafted; **Q3** open the PR on the tip after #340 and #346
   merge, with phase 2 on snapshot #5.
6. **Rule 10 rulings:** `PolyExpr.eval` is notation (2026-11-07; seal A canonical, seal B run with `SEAL_EVAL=1` and
   attributed); the `FinDist` coercion is notation (**DW-10 Q3**, 2026-11-17: strict-only failures it causes are recorded,
   not counted, not fixed); a projection `CoeFun`/`Coe` instance is notation (**coe-A canonical**, the strict variants run
   and attributed); reducible abbreviations are notation and are never requested by a seal; inside a file its own
   definitions may be read directly; the helper modules are foreign to each other and to `BonehBoyenSecurity.lean`.
7. **G44-01 precedent** (Gate 44): disclosure of a duplicate is not acceptance; an accepted duplicate needs Seyoon's
   recorded acceptance and a ledger row with its repayment.
8. **BS-F08** (decision-log row "bb1-sim statements: phase-1 review done"): Claude cloud sessions on this account share
   one commit-signing key, so a signature attests a Claude session on the account, not the maintainer; provenance rests
   on the pinned hashes and maintainer cherry-picks.
9. **Lean parallelism** (#353, `workflow.md` §4.1): cloud workers may run a pool; the worker's seal phase used a pool of
   3 (phase 1 checked the quoted text).

## What is frozen

From the issued brief (`records/…/issued-fill-r1/brief.md` § *The targets*, § *Scope*):
- **The four targets**: header (keyword to `:= by`) and statement prose before `**Proof sketch.**`. Permitted: each
  body; T2's and T3's sketch paragraphs (refreshed); `Relational`'s sketches may not change and did not.
- **`bb1_sidSecure`** (docstring, header and proof) and **`prob_simulate_rel`** are frozen whole.
- **`IB/BonehBoyenSecurity.lean`**: everything else, apart from one `import` per helper after the base's last import and
  a `## Contents` section in the module docstring that lists the helpers (T4's precedent).
- **`IB/Defs.lean`, `IB/BonehBoyen.lean`**: everything apart from the ten readers at their anchors.
- **Every other file**: `Games/Probability`, `Games/Hopping`, `Games/Simulate`, the rest of `Games/` and its facade,
  `Pairing/*`, T4's files, the facades, cleanup Stage 1's homes (including `Games/Bridges/Experiments`, which the fill
  imports), `EncryptThenTag/Forgery.lean` (DL-40), GSW and every other campaign.

## Questions for the audit

**1. True targets and correct proofs**
- **`expect_simulate_rel`** and **`expect_sample_rel`**: do the bodies establish the frozen statements for every
  `spec`, `σ`, `τ`, `R`, `c`, `G₀`, `G₁` (resp. `U`, `V`, `e`, `f₀`, `f₁`, `g₀`, `g₁`), with nothing else assumed? Is the
  induction's motive general enough (states generalized; the query case applying `h` with the induction hypothesis as
  the test-function agreement)?
- **T2.** Does the body establish the frozen bound for every `A`, `q`, `b`, `κ`, every generator and `ℓ`?
  - Is the bad event used **exactly** the statement's `(G.inst κ r).order < 2 ^ ℓ.eval κ`, and does its negation give
    `2^{idLen} ≤ p` (`bb1Scheme_idLen`, `BilinearGen.inst_eq`) and identity injectivity in `Z_p`?
  - Is the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]` sound on bad coins (two probabilities in `[0, 1]`) and is the
    good-coin equality `prob_sidGame_coins` true as stated, for all coins with `2^ℓ ≤ p` and `g ≠ 1`?
  - Step M: does `RelM` relate the real and simulated states exactly as design r1 §3.1's `R`, and do the nine `stepM_*`
    rows cover every call from every related state pair, including calls before `Init`, the target identity's key query,
    repeated and invalid challenges, and states with a recorded challenge but no identity? Is each bijection
    (`e ID`, `Equiv.addRight (b'/(ID − ID*))`, `Equiv.refl`) the right coupling, and is `ID − ID*` invertible wherever it
    is used?
  - Are E-h and E-c instances of `Games.expect_simulate_eager` with correct `used` predicates (`u.1.isSome`,
    `v.2.isSome`)? Is the `T` sample really unused after the pairing step (`expect_const`)?
- **T3.** Is the swap of `T` and `ρ` sound, is `T ↦ decodeT(M₁)⁻¹ decodeT(M₀) T` a bijection of the target group for
  every pair of valid messages, and are all other calls bit-independent (`bb1SimImpl_two_of_not`, in its generalized form
  with `bb1SimImpl false …` on the right)? What happens if no valid challenge is ever made?
- **Helpers.** Is any of the 58 `BB1Sim.*` helpers (or `bb1RealState_eq`) false, vacuous, or an assumption in disguise?
  The hypotheses carried into T2 are only `ho`, `hp`, `hg`, `he` (§ *What changed*); is each discharged from proved
  facts? Is `setup_out`'s existential used only inside one `κ`?
- **Sufficiency.** `bb1_sidSecure` (frozen, unchanged) is proved from T2–T4. With T2 and T3 proved, is its trace really
  free of `sorryAx` (phase 2: closure 20,373 constants, no direct `sorryAx` user; `collectAxioms` the standard three)?
- **Edge cases:** `κ = 0`; `ℓ(κ) = 0` (`2^0 ≤ p`, injectivity trivial); `q = 0`; `p = 1` or a degenerate group; identity
  strings colliding modulo `p` on bad coins; an adversary that never initializes, never queries or never challenges.

**2. Frozen-statement integrity** (`phase2/static/frozencheck-tip.out`, `phase2/statements/touched-after.tsv`,
`phase1/frozencheck.out`, `phase1/tools/frozencheck.py`)
- Phase 2's `frozencheck.py` (base → head) gives **12/12 PASS**: H1 the four headers byte-identical; H2 their statement
  prose byte-identical; H3 `prob_simulate_rel` and `bb1_sidSecure` identical whole; H4 both files identical after masking
  the bodies, the sketches, the five helper imports and `## Contents`. Its **8 controls** each FAIL as they must (sketch
  spilling into prose, a one-character T3 header change, an unpermitted import, an edit to `bb1_sidSecure`, a module
  docstring edit outside `## Contents`, an edit to `prob_simulate_rel`, a prose edit and a header edit in `Relational`),
  and the unchanged head PASSes. Do these checks show the statements and their prose unchanged?
- The declaration-level comparison of the 9 files (`touched-after.tsv`): **94 UNCHANGED, 4 CHANGED** (exactly the four
  targets), **10 ADDED** to existing files (the readers) and **59 NEW_FILE** (the 58 helpers and `bb1RealState_eq`). Is
  any other declaration of a frozen file touched?
- **decls2** (pinned `decls2.py` `fa81981a…`, base → head over the 9 files; `phase2/static/decls2-landing-vs-tip.tsv`):
  **69 ADDED, 0 CHANGED, 0 REMOVED** — the 10 readers, the 58 `BB1Sim.*` helpers and `BB1Sim.bb1RealState_eq`
  (`decls2-summary.txt`: readers 10, `BB1Sim.*` 59). With the location column dropped it is phase 1's 68 rows (against
  the patch base) plus `bb1RealState_eq`. None of the 69 is `private`; the five new files have no `private` declaration.

**3. The ten readers** (`phase2/static/inscheck-tip.out`, `phase2/tools/inscheck_tip.py`, `checks/pins.txt`)
- Phase 2's `inscheck_tip.py` (base = the tip, whose two files equal the patch base's): base hashes hold; each block is
  byte-identical to the approved one; one blank line precedes it; removing it restores the base byte for byte; the heads
  are `97ecb6e0…` (563 lines) and `88454d6f…` (760 lines): **PASS**. Its **12 controls** (6 per file: one character in a
  reader, an extra line elsewhere, an extra blank after the block, reader lines deleted, reader lines moved, a docstring
  edited) each FAIL.
- Are these exactly the ten approved readers, verbatim, at the approved anchors, with `rfl` or one-line proofs, formula
  docstrings and no attribute, and nothing else added to `Defs.lean`/`BonehBoyen.lean`? Is each needed (each has a paired
  control row, § 6)? Are their `cast`/`show … from rfl` steps definitional reads of the file's own definitions (permitted
  inside the owner), and not hidden unfolds for consumers?

**4. The landing edit LE-bsf1** (`phase2/landing/le-bsf1-applied.diff`, `phase1/le-bsf1-proposed.diff`): is it
docstring-only apart from the one added `rfl` reader, with no statement or proof change elsewhere? Is
`bb1RealState_eq` the right reader for an `abbrev` under policy §1, and is its formula docstring accurate? Do the 21 glue
notes and two formulas describe their declarations correctly, and is "a variant of the game of [BB04, §2.1]" accurate
for `bb1RealAt`/`bb1RealLazy`?

**5. Duplication** (recent gates graded undisclosed re-proofs of public lemmas, and disclosed ones without a recorded
acceptance, as **majors**)
- **DL-57** (accepted, Q1; `records/duplication-ledger-DL55-57.md`, `records/cleanup-stages-stage2.md`): the public
  `BB1Sim.sidSpec_rng_one`/`_two` (`BBS/Lazy.lean:89`, `:94`) have the same statements and proofs as T4's **private**
  `BB1Machine.sidSpec_rng_one'`/`_two'` (`IB/BonehBoyenMachine/Oracles.lean:77`, `:84`; `checks/dl57.txt`). Stage 2
  promotes `sidSpec_dom_*`/`sidSpec_rng_*` and `zeroBits_eq_cast` into `IB/Defs.lean` as `IBEScheme.*` and re-points both
  users (BSF-F07 adds `sidImpl_allOutputs_some`/`sidImpl_none_of_ne` as passengers). Is DL-57's record complete (both
  twins, the acceptance, the repayment)? Is any **other** T4 declaration (`BB1Machine.*`, `drawStep_*`, the `Oracles`
  readers) re-proved by a `BB1Sim` helper?
- **`Games/`** (the delivery REPORT's § *Overlap and reuse* and design r1 §2.4): `expect_simulate_congr`
  (`Games/Hopping.lean:384`) and `Games.expect_simulate_eager` (`:494`) are used, not copied; the averaging bound is the
  public `abs_expect_sub_le_expect` (`Games/Probability.lean:409`), not a third copy beside the private ETT one
  (`EncryptThenTag/Forgery.lean:515`, DL-40); `Bridge.expect_sample_pair` (`Games/Bridges/Experiments.lean:72`) is used.
  Are the lazy handlers (`bb1SimLazy`, `bb1SimLazyChal`, `bb1RealAt`, `bb1RealLazy`) and their `expect_*` instances
  re-proofs of a generic `Games` fact (for example `simulate_eq_of_abs`, the lazy/eager lemmas of `OracleFromPRF/Lazy`,
  `EncryptThenTag/Lazy`, `HashAndSign/OneQuerySampling`)? Note that the open cleanup Stage 1 (#355) adds
  `Games/Tapes.lean` (`expect_simulate_abs`, `freshImpl`, `tapeImpl`, simulation in law) and is not on the base; the
  phase-1 review cross-checked its 79 added names against the fill (`phase1/cs1-added-names.txt`: no shared name, none
  mentioned). Is there a substantive overlap anyway?
- **Mathlib and `Pairing/Group`:** `natCast_bitsToNat_injective` composes `CharP.natCast_injOn_Iio` with
  `bitsToNat_lt`/`bitsToNat_injective` (BS-F01 ruled the wrapper away from `Group.lean`); `exists_equiv_mul_pow`,
  `key_eq`, `F_target_eq`, `pair_pow_val_eq` compose `Pairing/Group` facts. T2's inline `h01` (`|x − y| ≤ 1` on `[0, 1]`)
  has no public counterpart by the review's search. Is any of them a re-proof of a Mathlib `ZMod`/`orderOf`/`Equiv` fact
  or of a `Group.lean` lemma?
- **Name clashes:** the phase-1 short-name scan (`phase1/shortname-scan.txt`, with 2 positive controls) finds none of the
  68 short names at the check base except T4's private primed twins; `bb1RealState_eq` is clash-free.

**6. Rule 10** (`phase2/rule10/`; the figures are in § *The replay*). Variants: **A** and **B** (B with
`SEAL_EVAL=1`, which also seals `PolyExpr.eval`), each in two **harnesses**, **strict** and **coe** (coe-A canonical).
- **Seals:** 36 = 9 owners × {A, B} × {strict, coe}, each rc 0 with 0 errors in both forms and install and EOF records.
  Are they canonical, closure-complete and bound to the head? Request counts equal the delivered table; LE-bsf1 adds no
  definition. The DW-10 Q3 list is empty (the `FinDist` coercion is sealed and causes no failure).
- **Paired controls** (`mkctl_bsf2.py` = the delivered `mkctl_bb1sim.py` plus the two `bb1RealState_eq` entries):
  per harness **32 probes = 8 owners × {A, B} × {sealed, unsealed}** (`Relational`, `Defs`, `BonehBoyen`,
  `BonehBoyenSecurity`, `Lazy`, `Coupling`, `Random`, `Chain`; **`Real` has no probe of its own**: its rows `RealAt`,
  `RealLazy` and the `bb1RealState_eq` entries are exercised in consumers' probes). Per harness, **485 sealed negatives**
  (**239** in the 8 seal-A probes, **246** in the 8 seal-B probes; B adds the `PolyExpr.eval` row in the 7 owners other
  than `Relational`), each failing **exactly once**; **1479** other entries (readers in sealed probes and every entry of
  the unsealed probes) with 0 errors; 0 stray errors; `ALL_OK True`. Across both harnesses: 64 probes and 970 sealed
  negatives. Rows include the 10 reader pairs (`SidZeroSpec`, `SidTwoSpec`, `SidOneQuery`, `SidTwoQuery`, `SidKeyNe`,
  `SidFresh`, `SetupEq`, `KeyGenBind`, `EncBind`, `EncCT`) and 5 helper-definition pairs (`SimLazy`, `SimLazyChal`,
  `RealAt`, `RealLazy`, `RelM`). Do the controls show that each reader is needed and that each helper definition is
  sealed for its consumers?
- **`bb1RealState_eq` has no sealed negative** (disclosed): `BB1RealState` is an `abbrev`, which the canonical seals never
  request (it is in 0 of the 36 request sets), so no unfolding of it can fail under a seal. Its two entries
  (`ctlRealState`, the unfolding by `rfl`; `ctlRealStateReader`, the reader) ran in 6 sealed and 6 unsealed probes per
  harness with 0 errors. Is that an adequate treatment of an abbrev's reader?
- **`RealReads` has no paired control** (BSF-F05, accepted): a `Prop` structure whose readers are its projections; its
  constructor `RealReads.mk._flat_ctor` is sealed in `BonehBoyenSecurity` (+8 requests over the base: the 5 helper
  definitions, 2 generated matchers and the constructor), and the consumers' seals pass.
- **Base seals:** 16 (4 existing owners × 4) at the check base, from the worker's evidence on the exchange, recounted in
  phase 1 (not re-run in phase 2; `Relational` 53/53/52/52 as at #351).
- **Explicit-unfold scan** over the 9 files: does any proof read a foreign definition other than through a published
  reader (`sidImpl`, `sidSpec`, `oracleImpl`, `bb1Scheme`'s fields and encodings, `bb1SimImpl`, `bb1SimChal`, `encCT`,
  `decodeT`, `Pairing/Group`'s operations, `simulate`, `expect`)?

**7. Sources and citations** (`checks/tags.txt`; `sources-r1.zip` `references/`)
- New tags occur only as `[BB04]`, `[BB04, §2.1]`, `[BB04, §4.1]`, `[BB04, §4.1, *Setup*]`, `[BB04, §4.4]` and
  `[BB04, proof of Theorem 4.1, …]` with the sub-labels *Setup*, *Phase 1*, *Challenge*, *Phase 2, Guess and the
  advantage*; no new `[PS10]`, `[BGZ09]` or `[Sho04]` tag. The phase-1 review's `quotes.py` found every [BB04] quotation
  in the DW-7 transcription (`46f8f7b1…`; 9 of 9, a fabricated control reported `MISSING`). Are the locators right
  against `references/boneh-boyen-2004-selective-id-ibe.md` (§2.1 p. 3, §4.1 p. 6, the proof of Theorem 4.1 pp. 7–8,
  §4.4 p. 8)? Is "[BB04, §4.2]" (the brief's alternative) or "proof of Theorem 4.1" the better locator for the
  simulator's computations?
- Is every glue note honest (a glue note claims no source), and does every fill-local variant say so
  (policy §2, *Deviations*)?
- T2's, T3's and `bb1_sidSecure`'s tags are frozen; `Relational`'s [BGZ09]/[Sho04] locators are #351's (DW-11).

**8. Docstrings, sketches and sizes**
- Every new public declaration has a docstring stating its formula in Lean argument order, with a tag or a glue note
  (`phase2/static/hygiene-landing.txt`: the only `no-tag/glue` rows are the three frozen `Relational` statement
  docstrings of #351). `hygiene.py` counts only `[BB04` as a tag (`phase1/tools/hygiene.py:61`): of those three,
  `expect_simulate_rel` and `prob_simulate_rel` carry [BGZ09]/[Sho04] tags, and `expect_sample_rel` carries neither a
  tag nor a glue note. All three are #351's frozen text (DW-11), outside this PR.
- Every proof of 15 lines or more carries a `**Proof sketch.**` (`phase2/lint/sk15-9files.txt`: the only hit is
  `BonehBoyen.lean:677 bb1SimChal_fresh`, #331's code, BM-F06, outside this PR). Do T2's and T3's refreshed sketches
  describe the delivered proofs (T2's names `setup_out`, `expect_simulate_rel` twice, both eager steps,
  `expect_sample_rel`, `CharP.natCast_injOn_Iio`, `abs_expect_sub_le_expect`; it drops the frozen sketch's
  `Games.expect_simulate_congr`, design §5 risk 3)? Do the module docstrings (title, *Main definitions*, *Main results*,
  *References*) and `BonehBoyenSecurity`'s `## Contents` describe the helpers?
- Sizes: every file at most 760 lines (cap 1000; `Coupling` 565 is the largest helper, within the 150–600 target); every
  line at most 100 characters.

**9. The replay and the axioms** (the merge-condition evidence; `phase2/replay/`, `phase2/axioms/`)
- Does the replay bind to the head `7a98ba01` (sources bound 19/19), and does it show no regression? Is anything necessary
  missing (a missing necessary piece of evidence is a **major**)? The raw seal and control logs are not in the pack
  (`POINTERS.md`); the summaries and their hashes are.

**10. Is anything undisclosed?** Among the five commits, the PR description, the two maintainer reviews, the delivery
REPORT and the records after them, is any change, claim or omission undisclosed? The known slips are listed below.

## The replay on snapshot #5 (maintainer phase 2, 2026-11-17, 07:44–09:08 UTC)

Recipe: `briefs/pass-shelat-ch5-8/maintainer/snapshots.md` (job recipe) and `workflow.md` §6.1. Tools: the recipe's
`olean-advance-a6d01b1b/tools-used/` (from `olean-rebase-evidence.zip` `b662b7da…`), byte-identical copies; Gate 44's
seal harness; phase 1's `decls2.py`, `inscheck.py`, `frozencheck.py`, `hygiene.py`; the delivered `mkctl_bb1sim.py` and
`Axioms.lean.txt`; new or adapted drivers in `phase2/tools/`, each with a header naming its change. One Lean process at a
time, slot-gated (fewer than 3 on the host). No `lake build`, no cache get.

- **Copy and overlay.** `cp -al` of snapshot #5 to `$SP/olean-replay-bb1sim` (1458 files, all hard links); 3346 Mathlib
  symlinks; NthRootLemmas built with rc 0 (olean `c0a9cff0…`). Snapshot #5 rehashed **0/0/0** before the copy, after the
  build and at the end.
- **Plan.** `stateplan init` at `3f540c22`: 1427 modules. `downorder.py`: changed 9, down 19. `fullorder.py`: **1432**
  (roots `TCSlib` and both `audits/*/Checks`). The plan builds **19** and reuses 1413: `Relational`, `Games`, `Defs`,
  `BonehBoyen`, `BonehBoyenMachine/{Draws,Words,Handler,Reduction,Oracles}`, `BonehBoyenMachine`, the five helpers,
  `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption` and root `TCSlib`. Neither `Checks` is downstream.
- **Build** (07:48:00–07:49:44): **19/19 rc 0**; `error:` 0, `error(` 0, substring "error" 0, `sorry` 0, warnings 0; no
  log/record mismatch (`permod.out`). Sources bound to `7a98ba01` 19/19.
- **State.** `stateplan update` 19; `check` over the full order **1432/1432, RESULT OK**, again at the end. All 19
  rebuilt oleans have link count 1.
- **Output map** (Mathlib excluded): **1463 entries**, SHA-256
  `b43812d0008b290343fab435f725544b1eef2c944f3581f2e8a62b3c0362171a`; against snapshot #5: 1454 equal, 4 changed
  (`Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity`), 5 added (the helpers), 0 removed. The other 10 rebuilt
  oleans are byte-identical to snapshot #5's.
- **Admissions** (`tipcensus.py`): tip `e1d39836` **196**, head **192**: **−4**, exactly `Relational` 2 → 0
  (`expect_simulate_rel`, `expect_sample_rel`) and `BonehBoyenSecurity` 2 → 0 (T2, T3); the five helpers have 0.
- **Axioms** (`AxiomsBsf.lean.txt` = the delivered probe plus `bb1RealState_eq` and a sorry control; rc 0; its one `sorry`
  warning is the control's):
  - `AXIOMS-LIST` **76 constants, 0 non-standard**: the 69 new ones, the four targets, `prob_simulate_rel`,
    `bb1_sidSecure` and T4 `exists_bb1_distinguisher`.
  - Census of the 9 owners: `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3, `Lazy` 24, `Real` 29,
    `Coupling` 20, `Random` 2, `Chain` 1 = **325 stored constants, 0 non-standard**.
  - `#sorry_trace`: **no direct `sorryAx` user** for `bb1_sidSecure` (closure 20,373), `bb1_sim_real` (15,352),
    `bb1_sim_random` (13,412), `expect_simulate_rel` (5,020), `expect_sample_rel` (11,705), `prob_simulate_rel` (5,023).
    `collectAxioms` gives `bb1_sidSecure` `[propext, Classical.choice, Quot.sound]`.
  - **Control:** `bsfSorryControl` is reported as its own direct `sorryAx` user and as `NONSTANDARD [sorryAx]`.
- **Rule 10** (`rule10_bsf2.sh`; `mkseals_ab`/`mkseals_coe`; `sealsum.py`):
  - **Seals: 36/36 rc 0, 0 `error:`, 0 `error(`**, install and EOF records present. Requests (strict A / strict B /
    coe A / coe B):

    | Owner | A | B | coe A | coe B |
    |---|---:|---:|---:|---:|
    | `Games/Relational` | 53 | 53 | 52 | 52 |
    | `IB/Defs` | 805 | 806 | 804 | 805 |
    | `IB/BonehBoyen` | 840 | 841 | 839 | 840 |
    | `IB/BonehBoyenSecurity` | 2320 | 2321 | 2319 | 2320 |
    | `BBS/Lazy` | 868 | 869 | 867 | 868 |
    | `BBS/Real` | 871 | 872 | 870 | 871 |
    | `BBS/Coupling` | 874 | 875 | 873 | 874 |
    | `BBS/Random` | 871 | 872 | 870 | 871 |
    | `BBS/Chain` | 877 | 878 | 876 | 877 |

    The `sealsum` tables equal the delivered ones (columns 1–6) in all four variants; the `mkseals` records differ only in
    `Real`'s stored-constant count, 28 → 29 (`bb1RealState_eq`).
  - **Paired controls** (`ctlcheck2.py`): strict and coe **ALL_OK True**, with the counts of § 6 (per harness 32 probes,
    485 sealed negatives each failing once, 1479 other entries with 0 errors). Every probe's per-control outcome equals
    the delivered `ctlcheck` exactly, apart from the two new entries.
  - **Explicit-unfold scan** (`scan1_g40.py`, `scan2.py`): **527 items** — 426 THEOREM, 85 LOCAL_OR_UNRESOLVED, 14
    OWNED_DEFINITION (each in its owner), 2 SIMPROC (`↓reduceIte`) — **0 foreign**, identical to the delivered summary.
- **Lint.** `campaign_style_lint --check8b TCSlib/Cryptography`: tip **92 FAIL / 104 WARN over 524 files**, head **92/104
  over 529**; the FAIL/WARN line sets are equal (`nonINFO.diff` empty). `style_lint` over the 9 files: 0 findings. `sk15`:
  the one base finding above.
- **Static at the head** (phase 2 § P2-2): decls2 69/0/0, reader insertion PASS with 12 controls, frozen check 12/12 with 8
  controls, hygiene clean.

## Known dispositions and slips (not findings)

- **The phase-1 review's findings** (`records/…/fill-final-r1/review.md`): BSF-F01 (minor, process: the worker's exchange
  final `e8b3388d` is SSH-signed again; the patches are unsigned and reproduce; a dispatch-template fix), BSF-F02 and
  BSF-F03 (minor; closed by LE-bsf1), BSF-F04 (minor, landing precondition; closed by DL-57 and Seyoon's acceptance of
  2026-11-17), BSF-F05 (info; `RealReads` has no paired control, stated in the PR description), BSF-F06 (info; the REPORT
  does not acknowledge the checkpoint-1 findings), BSF-F07 (info; placement of 9 scheme-generic facts in `BB1Sim`, folded
  into DL-57), BSF-F08 (info; merges and the shared `Games.lean`). **Grade them.**
- **Seal attempt 1 failed** before any Lean ran (`phase2/rule10/attempt1/`): the seal generators call
  `git -C <tree> show`, and the build export is not a repository. The driver then exported `GIT_DIR` (read-only use) and
  the seals were rerun in full (`rule10-phases.out`: `rule10_b rc=1` at 07:52:12, then `rc=0` 07:52:53–09:07:11).
- **About 140 MB of raw seal records, control sources and probe logs are not in any ZIP**; their SHA-256 are in
  `phase2/rule10/omitted-SHA256SUMS` and `phase2/scan/omitted-SHA256SUMS` (`POINTERS.md`). Seven large raw files of the
  phase-2 ZIP (scan items and kinds, state plan and records) are not copied into `verification-r1.zip`, but they are in the
  recorded phase-2 ZIP, whose manifest is here.
- **No seal or control was re-run for this pack.** Everything in `phase1/` and `phase2/` is the reviews' recorded
  evidence; `checks/` are git-object reads at staging.
- **Author dates.** The fourth worker commit (T2/T3, `40f7da54`) has author date 05:01:37, before the third
  (`469375fa`, 05:13:59); phase 1 reproduced the patches with committer dates taken per row of `COMMITS.tsv`.
- **The DL-57 ledger row** cites T4's twins at `Oracles.lean:78`, `:85`; they are at `:77`, `:84` at the base and the head
  (as in the review and the REPORT; `checks/dl57.txt`). Found at staging; the row's other content is right. In the same
  ledger table, DL-55 to DL-57 have five cells under a four-column header (a formatting slip inherited from earlier rows).
- **Phase 2's hygiene wording.** "Every helper docstring now has a `[BB04, …]` tag or a glue note"; the three
  `no-tag/glue` rows are `Relational`'s frozen docstrings, two of which do carry [BGZ09]/[Sho04] tags that the tool does
  not recognize (§ 8). Found at staging.
- **`rulings.md` Q8** says the bb1-sim gate covers the Games statement phase; the DW-11 ruling (2026-11-17) later moved #351
  and #352 out. The PR description's "per the design rulings (Q8)" refers to the gate as ruled after DW-11 (readers and
  fill).
- **Authorship.** The four fill commits were written by an external Claude cloud worker (lead; sub-agent A wrote
  `Coupling.lean`), delivered as patches, and cherry-picked and signed by the maintainer; LE-bsf1 is the maintainer's. The
  signing key is shared by the account's Claude sessions (BS-F08).
- **The PR description** (`pr357-description.md`) is the body as read with the GitHub tools at staging (REST `.body`, raw,
  and the MCP read; the same text). Its REST `base.sha` is `e1d39836`; only records commits have landed since.
- **Bundle.** `bundle.md` is on the exchange only, not in the records (`workflow.md` §3).

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees.txt` (`git merge-tree --write-tree`, git 2.43.0):

| Other side | Merge base | Result | Shared paths since the merge base |
|---|---|---|---|
| records pin `e6cdf4d4` | `e1d39836` | clean, tree `b5c1eda7…` | none |
| #347 `cleanup/dw5-derand-readers` `daa6e173` | `2da7e0f3` | clean, tree `778239f0…` | none |
| #355 `land/cleanup-stage1` `d3c7cb00` (stacked on #347) | `2da7e0f3` | clean, tree `b97f5329…` | `TCSlib/Cryptography/Games.lean` only |
| 6a `land/gsw-6a-o1` `a616adca` (local, unpushed, no PR) | `e1d39836` | clean, tree `d047b59c…` | none |
| 6a `land/gsw-6a-statements` `73aedcda` (local, unpushed, no PR) | `e1d39836` | clean, tree `a8941d86…` | none |

- `Games.lean` is shared with #355 only through the records history since the old base `2da7e0f3` (#351's `Relational`
  import, already on the tip); #357 itself does not touch it (its blob equals the pin's), and none of #357's 9 paths is
  touched by #347, #355 or the 6a branches.
- Three-way simulations: (pin × #347) × #357 and (pin × #355) × #357 are clean, change exactly the 9 files on the second
  step, and keep them blob-equal to #357's head.
- No `land/gsw-6a-*` branch exists on `origin` and no 6a PR is open at staging (`git ls-remote`; the open PRs are #347,
  #355 and #357).
- **Snapshot adoption.** `$SP/olean-replay-bb1sim` is adoptable as olean snapshot #6 only if the merge commit's Lean equals
  `7a98ba01`'s (map `b43812d0…`). If #355 (or any other code PR) merges first, the merge's Lean differs: `Chain` imports
  the Stage 1 home `Games/Bridges/Experiments`, which #355 extends, so #357 then re-replays on the new tip (phase-1
  checklist step 9). After merge, record the bb1-sim gate's outcome; DL-57 is already in the ledger.

## Evidence files

- **`pack-r1.md`** (this file), **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr357.diff.txt`**: `git diff e1d39836..7a98ba01`, equal byte for byte to the three-dot view (9 files, +1925/−21;
  SHA-256 `d494afbfefd8e6336d6b050fd3a7907ba9b2b2d81c6e8f481e440c7325bf82bc`).
- **`pr357-description.md`**: the PR body at staging (REST `.body`, raw).
- **`source-head-r1.json`**: the pins, the five commits, and for each of the 9 files its status, blob, SHA-256, line
  count at base and head, maximum width and over-width, tab and trailing-space counts.
- **`sources-r1.zip`**: `head-7a98ba01/` the 9 files; `base-e1d39836/` the 4 that exist at the base;
  `context-7a98ba01/` the unchanged TCSlib modules the 9 files import directly, plus T4's `Oracles.lean` (DL-57); and
  `references/` the BB04 transcription (DW-7) and the [BGZ09] and [Sho04] transcriptions. Its `README.md` gives every
  entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md` (layout and provenance), `POINTERS.md`, and `SHA256SUMS` (every other entry).
  - `phase1/`: the phase-1 review evidence ZIP, whole (manifest `SHA256SUMS.original`);
  - `phase2/`: the phase-2 evidence ZIP but for 7 large raw files (manifest `SHA256SUMS.original`;
    `sha256sum -c --ignore-missing`);
  - `checks/`: the git-object checks of this staging and their scripts;
  - `records/`: the bb1-sim design note, rulings, checkpoint-1 review, the final review and `phase2.md`, the issued brief
    with the approved reader blocks, Gate 44's two findings, `policy.md`, and extracts of the decision log (from the
    bb1-sim design note to #357), the duplication ledger (DL-55..DL-57) and cleanup Stage 2;
  - `pr/pr357-rest-fields.json`: the REST fields at staging.
- **`SHA256SUMS-r1`**: the files of this gate directory.

## Findings delivery

Return `gate48-bb1-sim-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The user
dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G48-01, G48-02, …**. Grade BSF-F01 to BSF-F08 in a separate table (agree, or regrade with the
reason). Report the audited head, the records pin, the counts by severity and a verdict: **CLEAR** (zero blockers and zero
majors) or **HOLD**. The gate closes at zero blockers and zero majors.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement or statement prose;
  - a reader beyond the approved ten, or a reader that is not a pure verbatim insertion at its anchor;
  - a forbidden read in a touched declaration not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof of a public one;
  - a fabricated source tag;
  - necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch or citation.
- **note:** anything else.
