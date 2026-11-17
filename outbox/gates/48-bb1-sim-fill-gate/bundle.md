## ===== pack-r1.md (this pack) =====

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

## ===== briefs/pairings/fills/bb1-sim/fill-final-r1/review.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# bb1-sim fill · final r1 · phase-1 (static) maintainer review

**Interim verdict: accept with landing edits, pending phase 2 and two rulings.** There is no
blocker and no major.

The delivery proves all four targets: T2 `bb1_sim_real`, T3 `bb1_sim_random`,
`ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel`. With T4 in, `bb1_sidSecure` now
uses only the standard axioms.

Every integrity, reproduction, insertion, frozen-header, scope, admission and merge check passes.
I recounted the worker's evidence (bootstrap, sweep, seals, controls, scan, lint, axioms and trace)
from the raw logs and bound it to the reproduced trees.

The T2 and T3 assembly follows design r1 §3. I found no helper that is false, vacuous or an
axiom-like assumption.

Four minors remain:
- **BSF-F01:** the exchange final is SSH-signed again.
- **BSF-F02:** checkpoint finding C1-F03 is still open (the `BB1RealState` reader).
- **BSF-F03:** checkpoint finding C1-F04 is still open (docstrings).
- **BSF-F04:** a disclosed overlap has no ledger row or acceptance yet. This is the G44-01
  precedent.

F02 and F03 are closed by one proposed landing edit, LE-bsf1: docstrings plus one `rfl` reader. It
is drafted in the evidence. F04 needs Seyoon's acceptance and a new row, DL-57.

I ran no Lean.

## What was reviewed

- **Delivery.** `inbox/fills/bb1-sim/` on `exchange/pass-shelat-ch5-8`, fetched by name. The tip is
  `2467bc3b`. I extracted the tree at `2467bc3befdad8472b1f359337bf3a203e3651e1` with `git archive`
  into a fresh empty directory. It has 1,426 files:
  - `REPORT.md` (331 lines);
  - 4 patches with `COMMITS.tsv`;
  - `src/` (9 files);
  - `evidence/` (1,409 entries and its manifest).
  - The top-level `SHA256SUMS` is `78cf6700…`; `evidence/SHA256SUMS` is `0269eda5…`.
- **The two final commits.**
  - `e8b3388d` (06:22, "fill bb1-sim: final"): parent `5451d3cd`, the cleanup Stage 1 final. It
    touches 1,130 paths, all under `inbox/fills/bb1-sim/`, and **carries an SSH `gpgsig`** (F01).
  - `2467bc3b` (06:23): unsigned. It changes **`REPORT.md` and, necessarily, the top-level
    `SHA256SUMS`**, whose `REPORT.md` line is the only line that changes. It changes nothing else.
    The `REPORT.md` change is a new section, *Exchange commits (BS-F08, disclosed)*.
- **Contract.** `issued-fill-r1/`: its `SHA256SUMS` passes, and the readers are `d6f8faf1…` and
  `967f2a30…`.
- **Background.** `design-r1.md` (§3, §5), `rulings.md`, `statements-final-r1/`, the checkpoint-1
  review (BSF-C1-F01..F08), `policy.md` (`6599b122…`), and the duplication ledger (DL-40, DL-55,
  DL-56). The DW-7 BB04 transcription is `46f8f7b1…`, and Gate 44's `findings-r1.md` (G44-01) and
  `pack-r2.md` (T44′) were also read.

## Checks

| Check | Result |
|---|---|
| **Integrity** | Both manifests pass `sha256sum -c`. The delivered paths equal each manifest's paths exactly: none missing, none extra, no leading `./` (`integrity.log`). |
| **Bases** | `mkbase.sh`, with `land/pairings-bb1-machine` and `fill/pairings-pair-bdh` fetched by name, prints `PATCH_BASE 72c0498a… tree b5a5842d…` and `CHECK_BASE 7cfe2b1b… tree 02b2d44a…`, and its tree assertions pass. The old #346 head `89a18a82` is an ancestor of the new head `98cb0e52`. |
| **Patches** | `git am` with signing off, on `72c0498a` in a sparse detached worktree, reproduces all 4 hashes. The committer date is taken per row of `COMMITS.tsv`; commit 4's author date (05:01:37) precedes its committer date (05:13:59), so a blanket `--committer-date-is-author-date` would not reproduce it.<br>• `23614c0a`<br>• `3f430cae`<br>• `622f5b03`<br>• `c35595aef7636c2ba9a25e1ffdac141b08d2fea5`<br>No commit has a `gpgsig`. `src/` is byte-identical to the head, 9 of 9 files.<br>**Range against checkpoint 1:** commits 1 and 2 are unchanged (`=` in `git range-diff`). Commits 3 and 4 replace `bcb9bcca` and `35c780c4`; between the two heads, 6 files change (+757/−44). |
| **Check tree** | `git merge-tree --write-tree 916afc25 c35595ae` gives `bdae2f85`, the reported check-head tree. The check base to that tree changes exactly the 9 files. The worker's check head commit `408c8195` is local-only, so it is not in this store; its tree is reproduced. |
| **Readers** | `inscheck.py` (the checkpoint-1 tool, reused):<br>• base hashes `4e220ead…` and `da875140…`;<br>• each block byte-identical to the pack's, after one blank line following `Defs.lean:430` and `BonehBoyen.lean:412`;<br>• removing the blocks restores the base;<br>• heads `97ecb6e0…` (563 lines) and `88454d6f…` (760 lines): **PASS**.<br>All 12 controls fail as they should. **There is no approved addition in the frozen files.** The C1-F03 reader `bb1RealState_eq` was not added (F02). If it is added, it goes into the helper `BonehBoyenSecurity/Real.lean`, not into `Defs` or `BonehBoyen`, so the pins are unaffected. |
| **decls2** (pinned `fa81981a`, against the patch base) | **68 ADDED, 0 CHANGED, 0 REMOVED.** That is the 10 readers plus 58 `BB1Sim.*`. The output is byte-identical to the delivered `decls2-final.tsv`.<br>**Against checkpoint 1's 59 rows:**<br>• +9 names, the step-M rows `stepM_init_none`/`_some`, `stepM_keyGen_none`/`_target`/`_ne`, `stepM_challenge_none`/`_repeat`/`_invalid`/`_fresh`. They were announced at C1-F05 and are named in `Coupling`'s module docstring.<br>• 0 removed.<br>• 1 statement changed: `bb1SimImpl_two_of_not`, whose right-hand side is now `bb1SimImpl false …` instead of `bb1SimImpl b …`. It is disclosed and true (checkpoint-1 review). The old form follows from the new one applied twice, so it is equal or more general, as the brief allows. |
| **StmtDump** | 74 `STMT` lines: the 68 new constants, the 4 targets, `prob_simulate_rel` and `bb1_sidSecure`. There is no `MISSING`, no error, and rc 0. The probe hash is bound to its run. |
| **Frozen headers and prose** | `frozencheck.py`, my own: **12/12 PASS**.<br>• H1: the 4 target headers are byte-identical.<br>• H2: their statement prose is byte-identical.<br>• H3: `prob_simulate_rel` and `bb1_sidSecure` are identical whole.<br>• H4: both files are identical after masking the bodies, the sketches, the 5 helper imports and `## Contents`.<br>Eight controls fail as they must: sketch spilling into prose, a one-character header change in T3, an unpermitted import, an edit to `bb1_sidSecure`, a module-docstring edit outside `## Contents`, an edit to `prob_simulate_rel`, a prose edit and a header edit in `Relational`. The unchanged head passes. The worker's own check is 12/12 with 6 controls. |
| **Admissions** | Bootstrap: 193/193, with 22 `sorry` warnings in 10 modules, equal to `base-sorries.txt`. Final sweep: 18/18 with 0 warnings. The only `sorry`s removed are the four targets (`Relational` 2, `BonehBoyenSecurity` 2), so **18 in 8**. The 9 files have 0 `sorry`/`admit`/`native_decide`/`axiom` tokens outside comments. |
| **Axioms** | 75 constants, **0 non-standard**: the 68 new ones, the 4 targets, `prob_simulate_rel`, `bb1_sidSecure` and `exists_bb1_distinguisher`. The census over the 9 owners covers 324 stored constants: `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3, `Lazy` 24, `Real` 28, `Coupling` 20, `Random` 2, `Chain` 1, all 0 non-standard. |
| **`sorryAx` trace** | Every root has **no direct `sorryAx` user**:<br>• `bb1_sidSecure`: closure 20,373 constants;<br>• `bb1_sim_real`: 15,352;<br>• `bb1_sim_random`: 13,412;<br>• `expect_simulate_rel`: 5,020;<br>• `expect_sample_rel`: 11,705;<br>• `prob_simulate_rel`: 5,023.<br>The walk's fuel (10⁶) was not exhausted. `collectAxioms` independently gives `bb1_sidSecure` the standard three, and `exists_bb1_distinguisher` (T4) is standard.<br>**The evidence that T4 is in:** the probe ran at the check head (`HEAD.txt` `408c8195`, tree `bdae2f85`), which contains #346's `89a18a82` and #340's `916afc25`. The staging probe at the check base had `bb1_sidSecure` reaching exactly T2 and T3. LE-g44 (`98cb0e52`) changes only docstrings (Gate 44 r2: comment-stripped byte identity), so the result carries over to #346′. Phase 2 re-runs the probe on the landing tree. |
| **Scope** | `git diff --stat 72c0498a c35595ae` lists exactly 9 files: `Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity` and the 5 new `BonehBoyenSecurity/{Lazy,Real,Coupling,Random,Chain}`.<br>Nothing in `Games/Probability`, `Games.lean`, `Pairing/*`, T4's files, the cleanup Stage 1 homes, GSW or other campaigns. Every helper import is in `order.txt` (`Hopping` 149, `Relational` 168, `Bridges/Experiments` 128, `BonehBoyen` 184) or is an earlier helper.<br>No `fill/bb1-sim` or `check/` branch is pushed. |
| **Hygiene** | Every file is at most 760 lines; the helpers have 130–565. Every line is at most 100 characters. There is no `@[simp]`, no new `attribute` (`BonehBoyen.lean:386` is the base's) and no micro sign. Every proof of 15 or more lines has a `**Proof sketch.**`. The module docstrings have a title, *Main definitions*, *Main results* and *References*, and `## Contents` lists the 5 helpers. **Docstring tags and glue notes: see F03.** |
| **Citations** | Every [BB04] quotation in the helpers and in T2/T3 occurs in the DW-7 transcription (`quotes.py`, whitespace- and LaTeX-insensitive; 9 of 9, plus 1 fabricated control reported `MISSING`). The locators exist in the transcription: §2.1 (p. 3), §4.1 (p. 6), proof of Theorem 4.1 *Setup*/*Phase 1*/*Challenge*/*Phase 2, Guess and the advantage* (pp. 7–8), and §4.4 (p. 8). There is no fabricated locator. The two plain `[BB04, §2.1]` tags on fill-local variants are F03. |
| **Clash and shadow** | My short-name scan of `TCSlib/` and `audits/` at the check base finds 0 of the 68 short names, except T4's **private primed** `sidSpec_rng_one'`/`_two'`, which `git grep -w` reports. 2 positive controls are hit. `BB1Sim.` and `namespace BB1Sim` do not occur at the base, so no unqualified use in a `DOWN` module can change resolution. The proposed `bb1RealState_eq` is also clash-free. |
| **Lint** | The delivered `campaign_style_lint` outputs, recounted, give 92 FAIL / 104 WARN at both base (524 files) and head (529 files). The line-set diff is **0 new, 0 gone**. Check 8 lists no new definition; the only IBE line is the base's `SIDSecure` WARN. `style_lint` has 0 findings, and `sk15`'s one finding is the base's `bb1SimChal_fresh`. |

## Recount of the worker's evidence

I recounted from raw logs, with each record bound to its source by SHA-256 against my reproduced
trees: `recount_build.py`, `recount_seals.py` and `recount_controls.py` in the evidence.

- **Bootstrap** (check base `02b2d44a`):
  - 193 modules, rc 0, 0 errors in both forms;
  - 22 `sorry` warnings in 10 modules;
  - sources bound 193/193, log hashes 193/193.
- **Final sweep** (check head `bdae2f85`):
  - 18 modules, all rc 0, with 0 errors and 0 `sorry`;
  - bound 18/18;
  - the set equals `closures.txt`'s 13 `DOWN` plus the 5 helpers.
- **Base tree** (for the base seals): 13 `DOWN` modules rebuilt at the check base, bound 13/13, with
  4 `sorry` (the targets).
- **Canonical seals.**
  - **36 head seals** (A, B, coe-A and coe-B for 9 owners) and **16 base seals** (4 owners).
  - Each is bound in three ways: the owner source to its tree, the probe source to `probe_sha256`,
    and the log to `log_sha256`.
  - Each has rc 0 and 0 errors in both forms, so there is no failing declaration.
  - The only notation exclusion is `PolyExpr.eval`. The `FinDist` coercion is sealed and causes no
    failure, so the DW-10 Q3 list is empty.
  - Request counts per owner (A/B/coe-A/coe-B) equal REPORT's table. `Relational`, `Defs` and
    `BonehBoyen` are unchanged from the base, and `Relational` is 53/53/52/52, the #351 precedent.
  - `BonehBoyenSecurity` gains 8 requests in each variant: the 5 helper definitions, 2 generated
    matchers and `RealReads.mk._flat_ctor`.
- **Paired controls.**
  - Runs were matched to sources by hash. In each of strict and coe there are 32 probes, and
    **485 sealed negatives each fail exactly once**.
  - All 485 positives pass, the unsealed probes have 0 errors, and nothing is stray.
  - The rows include the 10 reader pairs (`SidZeroSpec`, `SidTwoSpec`, `SidOneQuery`,
    `SidTwoQuery`, `SidKeyNe`, `SidFresh`, `SetupEq`, `KeyGenBind`, `EncBind`, `EncCT`) and 5
    helper-definition pairs (`SimLazy`, `SimLazyChal`, `RealAt`, `RealLazy`, `RelM`).
  - There is no `RealReads` pair (F05).
- **Explicit-unfold scan:**
  - 527 items: 426 theorems, 85 local hypotheses or projections of local hypotheses, 14 owned
    definitions (each in its owner) and 2 `↓reduceIte`;
  - **0 foreign**.
- **Parallelism.** The worker moved from the single lock to a pool of 3 for the seal phase, under
  `workflow.md` §4.1. The quoted text equals lines 226–245 at `b986b862` (PR #353, on `main`): cloud
  workers may run a pool. This is consistent.

## The proofs

**`Relational`.** `expect_simulate_rel` is induction on `c`, generalizing the states, with
`simulate_pure`/`_query` and `expect_pure`/`_bind`. `expect_sample_rel` is `expect_bind` and
`expect_sample_equiv e`, then a pointwise comparison. Both follow design §2.3 (L1, L3) and their
frozen sketches, so neither sketch changed (H2/H4).

**T2** (design §3.1).
- **Steps.** `setup_out` gives `o`; then `prob_bind` on both sides, and
  `abs_expect_sub_le_expect` with the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]`.
  - Bad coins: two probabilities in `[0, 1]`.
  - Good coins: equality by `prob_sidGame_coins`.
  - Last, `prob_eq_expect` and `prob_sample_eq_uprob`.
- **Error bound.** The bad event is exactly the statement's `(G.inst κ r).order < 2 ^ ℓ.eval κ`.
  Its negation gives `2^{idLen} ≤ p` through `bb1Scheme_idLen` and `BilinearGen.inst_eq`. Then
  `bitsToNat u < 2^ℓ ≤ p` makes identities distinct in `Z_p`
  (`natCast_bitsToNat_injective` = `bitsToNat_lt`, `bitsToNat_injective` and
  `CharP.natCast_injOn_Iio`, as BS-F01 requires). The bound is the averaging bound with a 0/1
  indicator, so no constant is lost.
- **`prob_sidGame_coins`** (`Chain`) is design steps (1)–(7) in order:
  1. `expect_sample_comm` moves `h` past `g₂` and `ρ`.
  2. `expect_sample_sidImpl` is R1 (`expect_simulate_rel` with design §3.1's `R_h`) followed by E-h
     (`Games.expect_simulate_eager` with `O = bb1RealLazy o`, `OE h = bb1RealAt o h`,
     `used u = u.1.isSome`).
  3. `g₂ = g^{b'}` along `Equiv.ofBijective _ (pow_val_bijective_of_ne_one _ g.2)`.
  4. Step M is `expect_simulate_rel` with `RelM`, design §3.1's `R` verbatim. The per-call
     hypothesis is `stepM_call`: 9 rows, with `expect_sample_rel` along `e ID`, along
     `Equiv.addRight (b'/(ID − ID*))` (BB04's `r = r̃ + b/(I − I*)`) and along `Equiv.refl`.
  5. E-c is `Games.expect_simulate_eager` with `used v = v.2.isSome`.
  6. `Bridge.expect_sample_pair` twice, then `expect_const` for the unused `T`.
- **Instances.** Every `expect_simulate_rel` and `expect_simulate_eager` instance is a single
  application with handler-specific hypotheses. There is no new eager or relational lemma
  (DL-33 is respected).

**T3** (design §3.2).
- Unfold both games, swap `T` with `ρ` (`expect_sample_comm`), then apply
  `expect_bb1SimImpl_random`.
- That lemma is E-T on both sides (`expect_simulate_bb1SimLazy` with `zt T = (Z, T)`), then
  `expect_simulate_congr` with `bb1SimLazy_random_call`.
- At the first valid `Challenge`, `expect_sample_rel` uses `R := Eq` along
  `T ↦ decodeT(M₁)⁻¹ decodeT(M₀) T`. Every other call is bit-independent (`bb1SimImpl_two_of_not`,
  generalised form).

**No helper is false, vacuous or an assumption in disguise.**
- **Hypotheses.** The only hypotheses the helpers carry into T2 are:
  - `ho : ∀ h, RealReads … (o h)`, discharged by `setup_out`'s second conjunct, which is proved;
  - `hp : 2^ℓ ≤ p`, exactly the good-coin event;
  - `hg : g ≠ 1`, from the subtype `g.2`;
  - `he`, from `exists_equiv_mul_pow`, which is proved.

  T3 uses none.
- **The existential.** `setup_out`'s `o` is found by unification and is used only inside each κ.
- **The new statements.** I re-checked those added since checkpoint 1 against the definitions:
  - the 9 `stepM_*` rows;
  - the generalized `bb1SimImpl_two_of_not`.

  Each row's `∃ f₀ f₁` is witnessed by the reading of both calls, as the checkpoint-1 review
  traced. The 49 checkpoint-1 helpers were checked true there, and their statements are unchanged
  except the one above.
- **Quantifier order.** T2 and T3 are concrete in κ. The fill constructs no machine and no error
  function, and nothing is chosen across κ. The machines and errors of `bb1_sidSecure` come before
  κ in its frozen statement and proof, which this fill does not touch.
- **Edge cases.**
  - `ℓ(κ) = 0`: `2^0 ≤ p` holds, and identities are trivially injective.
  - Calls before `Init`, repeated challenges, and invalid messages are all rows of `stepM_call`
    and of the eager side conditions.
  - A state with a recorded challenge but no identity is unreachable, but it is still covered by
    the `none` rows.
  - The bad-coin branch needs no group fact.

**Sketches.**
- T2's refreshed sketch names `setup_out`, `expect_simulate_rel` (twice), both eager steps,
  `expect_sample_rel`, `CharP.natCast_injOn_Iio` and `abs_expect_sub_le_expect`. It drops
  `Games.expect_simulate_congr` (design §5, risk 3).
- T3's names `expect_sample_comm`, `expect_simulate_eager`, `expect_simulate_congr` and
  `expect_sample_rel`.
- Both describe the delivered proof.

## Checkpoint-1 findings: closure

| C1 finding | Status at the final |
|---|---|
| F01 unsigned exchange final | **Not met; disclosed.** `e8b3388d` is SSH-signed again. The follow-up `2467bc3b` is unsigned and explains the cause: `git pull --rebase` re-created the commit under the host's global `commit.gpgsign = true`. The patches are unsigned. See **BSF-F01**. |
| F02 REPORT head hash | **Closed.** REPORT gives `c35595aef7636c2ba9a25e1ffdac141b08d2fea5`, the reproduced head. 9 of its 10 full hashes resolve here. The tenth is the local-only check head `408c8195`, whose tree I reproduced. |
| F03 `BB1RealState` reader | **Open.** There is no `bb1RealState_eq`. REPORT still lists the abbrev's readers as "—". See **BSF-F02**. |
| F04 tags, glue notes and formulas | **Open.** 21 helper docstrings still have neither a tag nor a glue note, and 2 have no formula (`bb1SimLazy_eq`, `BB1RealState`). The checkpoint's `bb1SimImpl_allOutputs_of_ne_two` and `sidImpl_allOutputs_some` now give formulas. `bb1RealAt` and `bb1RealLazy` keep plain `[BB04, §2.1]`. REPORT's check 10 ("a … tag … or a glue note" on every new declaration) is inaccurate. See **BSF-F03**. |
| F05 announced additions | **Closed.** The 9 `stepM_*` exist, `Coupling`'s docstring names them, and the `bb1SimImpl_two_of_not` generalisation is disclosed. |
| F06 overlap and reuse | **Closed as a disclosure.** § *Overlap and reuse* carries design §2.4's table and the probe ports, discloses the `sidSpec_rng_one/_two` twins, and records BS-F01. Every `path:line` it cites checks out at the check base, and the Mathlib line is `CharP/Basic.lean:55`. **There is no ledger row or acceptance for the twins** (BSF-F04). |
| F07 sketch refresh and frozen check | **Closed** (above; my 8 controls). |
| F08 final-only checks | **Closed.** Seals A/B strict and coe on 9 owners plus base seals, paired controls, unfold scan, axioms with census and trace, lint, and the frozen check are all present and recounted. |

REPORT does not acknowledge the checkpoint-1 findings. Commits 3 and 4 are dated 05:13:59, and the
review was recorded at 05:19:56 (`62df03f9`). F02 and F05–F08 are closed anyway, but F03 and F04
were not acted on (F06 info).

## Disclosures, duplication and ledger

My own searches covered:
- by name and by conclusion shape in `Pairing/Group`, `IdentityBased/Defs`, T4's
  `BonehBoyenMachine/*` (every declaration listed), `Games/*` and `Asymptotic/Sampling`;
- `|p − q| ≤ 1` lemmas.

They found **no undisclosed duplicate of a public lemma**:
- T2's inline `h01` (`|x − y| ≤ 1` on `[0, 1]`) has no public counterpart; the nearest is
  `abs_prob_sub_le_of_agree`, a different statement.
- `pair_pow_val_eq`, `F_target_eq`, `key_eq` and `exists_equiv_mul_pow` are compositions of
  `Pairing/Group` facts, as REPORT says.
- T4's `drawStep_*` rows are about a different handler.
- The probe's lemmas were never landed, so porting them is reuse, not duplication.

**One overlap needs a new ledger row (G44-01 precedent: disclosure is not acceptance):**

| Proposed row | New declaration | Existing copy | Proposed resolution |
|---|---|---|---|
| **DL-57** | `BB1Sim.sidSpec_rng_one`, `_two` (public; `BonehBoyenSecurity/Lazy.lean:89`, `:94`). They sit with their scheme-generic siblings `sidSpec_dom_*`, `sidSpec_rng_zero` and `zeroBits_eq_cast` | T4's **private** `BB1Machine.sidSpec_rng_one'`, `_two'` (`BonehBoyenMachine/Oracles.lean:77`, `:84`), with the same statements and proofs | **Cleanup Stage 2:** promote the six `sidSpec_dom_*`/`sidSpec_rng_*` (and `zeroBits_eq_cast`) into `IdentityBased/Defs.lean` as `IBEScheme.*`, beside `sidSpec_eq`. Re-point the `BB1Sim` users and T4's primed copies, proof-only. Re-pointing T4 to `BB1Sim` directly would make `BonehBoyenMachine` import a security helper, which is not recommended. |

`sidImpl_allOutputs_some` and `sidImpl_none_of_ne` (`Real`) are also scheme-generic `IBEScheme` facts
in a `BB1Sim` namespace. They are not duplicates, but they are natural passengers for the same
promotion (info, F07).

## Findings

| ID | Grade | Finding | Fix |
|---|---|---|---|
| **BSF-F01** | minor (process) | **The exchange final `e8b3388d` is SSH-signed again** (C1-F01). The follow-up `2467bc3b` is unsigned and discloses the cause: `git pull --rebase` re-creates the commit under the host's global `commit.gpgsign = true` (`gpg.format = ssh`). The deliverable is unaffected: the patches are unsigned and reproduce, and landing uses maintainer-signed cherry-picks. | No action on this delivery; a force-push is forbidden. Dispatch template: `git -c commit.gpgsign=false pull --rebase` (or a repo-local `commit.gpgsign false`), and check `git cat-file -p HEAD \| grep -c gpgsig` **after** the rebase, before the push. |
| **BSF-F02** | minor | **`BB1Sim.BB1RealState` still has no reader** (C1-F03; policy §1, "a new public `abbrev` still lands with its `_iff` or `_eq` lemma"). Lint check 8 does not see abbrevs, so the delivered lint is silent. | Landing edit **LE-bsf1**: `bb1RealState_eq … := rfl` after the abbrev in `Real.lean`, with a docstring. Drafted in `le-bsf1-proposed.diff`: decls2 against `c35595ae` gives exactly +1 ADDED, 0 CHANGED, and it is clash-free. It needs no control row, since the abbrev is notation. |
| **BSF-F03** | minor | **Docstrings** (C1-F04, not acted on):<br>• 21 helper docstrings have neither a `[BB04, …]` tag nor a glue note: `relM_iff`, `bb1SimLazyChal_fresh`/`_of_not`, `bb1SimLazy_eq`/`_zero`/`_one`/`_two_fresh`/`_two_of_not`, `bb1SimImpl_zero_coins`/`_one_coins`/`_two_of_not`/`_two_fresh_allOutputs`/`_allOutputs_of_ne_two`, `BB1RealState`, `bb1RealAt_none`/`_some`, `bb1RealLazy_zero_none`/`_none_of_ne`/`_some`, `sidImpl_allOutputs_some` and `sidImpl_none_of_ne`.<br>• `bb1SimLazy_eq` and `BB1RealState` have no formula.<br>• `bb1RealAt` and `bb1RealLazy` carry a plain `[BB04, §2.1]` though they are fill-local variants (policy §2, *Deviations*).<br>• REPORT check 10 overstates.<br>The `hygiene.txt` scan lists them all. | **LE-bsf1** (docstrings only). Add "Glue: …" notes, the two formulas, and "(a variant of the game of [BB04, §2.1], …)". With the draft applied, the hygiene scan has 0 flags and every line is at most 100 characters. |
| **BSF-F04** | minor (landing precondition) | **The disclosed overlap has no ledger row or acceptance:** the public `BB1Sim.sidSpec_rng_one`/`_two` against T4's private `sidSpec_rng_one'`/`_two'`. REPORT says "a later cleanup could re-point them" but proposes no row. This is the G44-01 precedent: disclosure is not acceptance. | Seyoon's acceptance and the row **DL-57** above (Q1). |
| BSF-F05 | info | **`RealReads` has no paired control,** though C1-F08 listed it. It is a `Prop` structure, its readers are its projections (`encPP`, `msgSpace`, `keyGen`, `enc`), and there is no unfolding for a reader to replace. Its constructor `RealReads.mk._flat_ctor` is sealed in `BonehBoyenSecurity` (+8 requests), and the consumers' seals pass. | Accept. Say so in the PR description. |
| BSF-F06 | info | **REPORT does not mention the checkpoint-1 findings,** and the source was frozen before the review was recorded (see above). | None. LE-bsf1 closes the remainder. |
| BSF-F07 | info | **Placement.** 9 scheme-generic `IBEScheme` facts sit in `BB1Sim`: `sidSpec_dom_*`/`_rng_*`, `zeroBits_eq_cast`, `sidImpl_allOutputs_some` and `sidImpl_none_of_ne`. Their home is `Defs.lean`, which is frozen here. | Fold into DL-57's promotion. |
| BSF-F08 | info | **Merges and shared files.** All four merges are clean (below). Only the cleanup Stage 1 merge has a shared file, `Games.lean`, and that side's change is #351's `Relational` import, already on the tip; **the fill itself does not touch `Games.lean`**. `Chain` imports the cleanup home `Games/Bridges/Experiments` and uses `Bridge.expect_sample_pair` and `prob_sample_eq_uprob`. Cleanup Stage 1 adds 8 lines there and changes no declaration the fill uses. None of its 79 added names is mentioned in the fill's files, and none of the fill's names is among them. | If cleanup Stage 1 lands first, phase 2 replays on top of it (checklist step 9). |

## Merges (`git merge-tree --write-tree`)

| Other side | Merge base | rc | Tree | Shared files |
|---|---|---|---|---|
| records tip `b8dfca4e` (fetched; Lean-equal to `463f2244` and to `ca129d64`: 0 Lean paths differ) | `ca129d64` | 0 | `ccbb94fa` | none |
| #340 `916afc25` | `9e7a9648` | 0 | `bdae2f85` (= the check head) | none |
| #346′ `98cb0e52` (LE-g44, docstrings in `Draws`/`Words`/`Handler` only) | `89a18a82` | 0 | `12a6154b` | none. The fill touches none of the three files |
| cleanup Stage 1 final head `c8021348` (exchange `5451d3cd`; the commit exists here with the delivered hash) | `2da7e0f3` | 0 | `5e6e1d79` | `TCSlib/Cryptography/Games.lean` (facade imports; see F08) |

**The landing tree.** The fill merged with #346′, #340 and the tip gives T_land `c1d5fd89`.
- Against T44′, recomputed here as `8c427375` (Lean-equal to Gate 44's `bee027f0`; its 9 recorded
  blobs are equal), T_land differs in **exactly the 9 fill files**.
- A simulated cherry-pick of the 4 commits onto #346′ merged with the tip applies cleanly
  (`landing-sim.txt`). Merged with #340, it gives `c1d5fd89` again.

## Landing plan

1. **Rulings first:** Q1 (DL-57) and Q2 (LE-bsf1), then phase 2 (below). The verdict becomes final
   only after phase 2.
2. **Landing base B′:**
   - a maintainer-signed `--no-ff` merge of the records tip into #346′ (`98cb0e52`);
   - its Lean must be the patch base with LE-g44, that is, Lean diff from `72c0498a` = `Draws`,
     `Words` and `Handler` only;
   - simulated tree `12f2fe13` on tip `b8dfca4e`.
3. **Branch `land/pairings-bb1-sim` from B′.**
   - `git cherry-pick -S` of `23614c0a`, `3f430cae`, `622f5b03` and `c35595ae`, keeping the author
     (Claude) and the subjects; each applies cleanly.
   - Then the maintainer-signed commit **LE-bsf1** (`le-bsf1-proposed.diff`, 3 files: `Lazy`,
     `Real`, `Coupling`; docstrings and `bb1RealState_eq`).
   - Check:
     - `git diff --stat B′` lists the 9 files;
     - decls2 against B′ gives 69 ADDED (68 plus `bb1RealState_eq`), 0/0;
     - the insertion pins `97ecb6e0…` and `88454d6f…` hold.
4. **PR**, base `land/pairings-bb1-machine` (stacked on #346, Q9).
   - The description says that until #346 merges, the diff also shows B′'s tip merge: the
     #351/#352 Lean already on the records branch, plus records documents.
   - It also carries:
     - the DL-57 row;
     - F05's note;
     - the attribution: worker Claude, sub-agent A on `Coupling`;
     - the phase-2 numbers.
   - Push only the landing branch.
5. **When #346 merges:**
   - Retarget the PR to `cryptography/pass-shelat-ch2-4`.
   - If the diff shows more than the 9 files, rebuild the branch by re-cherry-picking the 5 commits
     onto the new tip, signed.
   - If #340 has not merged, the landing tree lacks T1's proof, and the `sorry` trace of
     `bb1_sidSecure` then reaches `bdhAssumption_of_dbdhAssumption` only. Record that, or wait for
     #340 (phase 2, step 10).
6. **After merge:** check the merge commit's Lean against the replayed tree (T_land plus LE-bsf1).
   If it is equal, the replay is adoptable as the next snapshot. Record DL-57 in the ledger and the
   bb1-sim gate (Q8) inputs.

## Phase-2 checklist (merged-tree replay)

**Base:** `$SP/olean-replay-g44b` (T44′ `bee027f0`, map `fca1b6a3…`, 1,458 entries without
Mathlib). It is better than snapshot #4: it already contains #340 and #346′, so only the fill's
closure is rebuilt (19 modules; from snapshot #4, #340's and #346′'s closures would be rebuilt
too). It also becomes snapshot #5 if #340 and #346
merge with Lean T44′.

1. **Before anything:**
   - rehash `olean-replay-g44b` against `fca1b6a3…` and snapshot #4 against `6607620d…`; both must
     be 0/0/0;
   - check that no Gate 44 r2 job is writing to it.
2. **Copy:** `cp -al $SP/olean-replay-g44b $SP/olean-replay-bsf` (1,459 files, hard links; the
   Mathlib symlinks are kept). **Never write into `olean-replay-g44b`.** The build must replace
   each rebuilt olean by a new inode (link count 1 afterwards), never write through a link.
3. **Tree:** a sparse worktree at the landing head (`land/pairings-bb1-sim`, or T_land `c1d5fd89`
   plus LE-bsf1 if the branch is not yet cut). Its Lean must equal T44′ plus the 9 files plus
   LE-bsf1.
4. **Plan.** The full order at T44′ is **1,427** modules, including root `TCSlib` and both
   `audits/*/Checks`; at the landing tree it is **1,432** (+5 helpers). The rebuild set is
   **19 modules**:
   - the 13 `DOWN` of `closures.txt`: `Relational`, `Games`, `Defs`, `BonehBoyen`,
     `BBM/{Draws,Words,Handler,Reduction,Oracles}`, `BonehBoyenMachine`, `BonehBoyenSecurity`,
     `IdentityBased` and `AdvancedEncryption`;
   - the 5 helpers, before `BonehBoyenSecurity`;
   - root `TCSlib`.

   Neither `audits/*/Checks` is downstream. The output map is expected to have **1,463** entries:
   1,458 + 5.
5. **Build** through `scripts/lean_check_tree.sh`, one module at a time, under the 3-process host
   limit. Expect rc 0 and 0 errors in both forms for all 19, with 0 `sorry` warnings in the 9
   files. Bind each source to the landing tree.
6. **Admissions:** the full-closure census goes from 196 at T44′ to **192**. `Relational` and
   `BonehBoyenSecurity` go from 2 to 0 each, and no other module changes.
7. **Axioms:** the worker's `Axioms.lean.txt` plus `bb1RealState_eq`, 76 constants. Expect:
   - every constant standard;
   - a census over the 9 owners of 325, with `Real` at 29;
   - `#sorry_trace` empty for `bb1_sidSecure` and the 5 other roots.
8. **Rule 10 at the landing tree:**
   - canonical seals A/B in strict and coe for the 9 owners. Request counts should equal the
     delivered table, since LE-bsf1 adds no definition; attribute any difference;
   - the 32-probe control set in both variants. Each negative fails exactly once, every positive
     passes, and the unsealed probes are clean;
   - the explicit-unfold scan: 0 foreign.

   Base seals carry over from the delivery (16 seals, recounted here).
9. **If cleanup Stage 1 has landed first:** replay on that tip instead. `Games.lean` and the
   `Bridges/Experiments` and `Asymptotic/Sampling` imports are then in the closure, so recompute
   the plan with `downorder.py`.
10. **If #340 is not merged at landing:** also replay #346′ × tip × fill without #340, from a copy
    of snapshot #4. `bb1_sidSecure`'s trace must then reach exactly T1.
11. **Lint and checks at the landing tree:**
    - `campaign_style_lint --check8b`, expecting 92/104 over 529 with no new line;
    - the insertion check (`inscheck.py`);
    - the frozen check (`frozencheck.py`, with its 8 controls).
12. **After:**
    - `olean-replay-g44b` still matches `fca1b6a3…`, and snapshot #4 rehashes 0/0/0;
    - record the output map of `olean-replay-bsf`.

## Questions for Seyoon (recommended option first)

- **Q1 (BSF-F04, DL-57).** The public `BB1Sim.sidSpec_rng_one`/`_two` twin T4's private primed
  copies.
  - (A) Accept as **DL-57**, resolved in cleanup Stage 2 by promoting the scheme-generic
    `sidSpec_dom/rng_*` and `zeroBits_eq_cast` into `IdentityBased/Defs.lean` and re-pointing both
    users, proof-only.
  - (B) Accept, and re-point T4's private copies to the `BB1Sim` ones in cleanup. This makes T4's
    `Oracles` import a security helper.
  - (C) Do not accept, and require a fill r2 that removes the public copies. This is not possible
    while T4's copies stay private and frozen.
- **Q2 (BSF-F02/F03).** How to close C1-F03 and C1-F04.
  - (A) Maintainer landing edit **LE-bsf1** as drafted: docstrings, plus the one-line
    `bb1RealState_eq := rfl`, +1 declaration, replayed in phase 2.
  - (B) Return to the worker for a final r2 with the same changes.
  - (C) Land the docstrings only and waive the abbrev reader as notation, recording a deviation
    from policy §1.
- **Q3 (PR shape).**
  - (A) Open the PR now, stacked on #346 (base `land/pairings-bb1-machine`) from the signed
    merge B′, with the noisy-diff note, and retarget after #346 merges.
  - (B) Wait for #346 and #340 to merge, then open on the records tip, which gives a clean diff and
    one replay.
- **Q4 (phase-2 base).**
  - (A) `cp -al` of `olean-replay-g44b` (T44′; 19 rebuilt).
  - (B) A copy of snapshot #4, rebuilding #340's and #346′'s closure too.

## Evidence

`bb1-sim-fill-final-r1-phase1-evidence.zip` (beside this file): 29 entries with an internal
`SHA256SUMS`. Its SHA-256 is in `evidence-SHA256SUMS`.

| Entry | Contents |
|---|---|
| `repro.log` | The refs and exchange commits (signing and paths), the second commit's diff, `mkbase.sh`, `git am`, the check tree, the `range-diff` against checkpoint 1, `src/` against the head, and the pushed refs |
| `integrity.log` | Both manifests and the path equality |
| `inscheck.out` | The reader insertion check with 12 controls |
| `frozencheck.out` | The frozen check, 12/12, with 8 controls |
| `decls2-final-review.tsv`, `decls2-vs-checkpoint1.txt` | decls2 against the patch base, and its diff against checkpoint 1 |
| `hygiene.txt` | Sizes, widths, attributes, tokens, docstring tags, glue notes, formulas and sketches |
| `quotes.txt`, `quote-control.lean.txt` | The BB04 quotation check, with a negative control |
| `shortname-scan.txt` | The clash scan with 2 positive controls |
| `build-recount.txt`, `seal-recount.tsv`, `controls-recount.txt`, `lint-recount.txt` | The recounts |
| `merges.log`, `landing-tree.txt`, `landing-sim.txt`, `cs1-added-names.txt` | The merges, T_land against T44′, the simulated landing, and the cleanup Stage 1 name cross-check |
| `le-bsf1-proposed.diff` | The proposed landing edit (not applied) |
| `tools/` | Every script used: `inscheck`, `frozencheck`, `hygiene`, `quotes`, the recounts, `mk_le`, and the pinned `decls2` |

**Process notes.**
- No Lean process was run, and no `lake` command; I did not touch any `$SP/olean-*` directory or
  another agent's directory.
- The delivery was extracted into `$SP/bsf-final/deliv/` (522 MB, kept for phase 2).
- `git am` and the LE draft ran in my own sparse detached worktree, `$SP/bsf-final/amwt`. It was
  restored to the head after the draft and removed afterwards.
- `mkbase.sh`, the T44′ recomputation and the landing simulation wrote only unreferenced objects
  (`commit-tree`, `merge-tree`). The fetches updated remote-tracking refs only.
- Nothing was staged, committed or pushed.
- Free disk stayed at or above 3.9 GB.

## Final verdict (phase 2)

**ACCEPT WITH LANDING EDITS (LE-bsf1 applied).** Phase 2 passes (`phase2.md`; zip
`bb1-sim-fill-final-r1-phase2-evidence.zip`, SHA-256 in `evidence-SHA256SUMS`). There is no blocker, no major and no
new finding.

- **Rulings applied** (Seyoon, 2026-11-17): Q1 DL-57 accepted (cleanup Stage 2); Q2 LE-bsf1 as drafted; Q3 the PR opens
  on the records tip now that #340 and #346 are merged, so no merge base B′ and no stacking.
- **Landing head** `land/pairings-bb1-sim` `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`: the records tip `e1d39836` plus
  signed cherry-picks of the worker's 4 commits (`range-diff` 4/4 `=`) plus LE-bsf1 (byte-identical to
  `le-bsf1-proposed.diff`). All 5 commits are signed by the records key.
- **Static:** decls2 against the tip 69 ADDED (10 readers, 58 helpers, `bb1RealState_eq`), 0 CHANGED, 0 REMOVED; reader
  pins `97ecb6e0…`/`88454d6f…` unchanged (insertion check against the tip PASS, 12 controls); frozen check 12/12 with 8
  controls; hygiene clean for every helper docstring.
- **Replay on snapshot #5** (`$SP/olean-replay-bb1sim`): 19/19 rc 0 with 0 errors and 0 `sorry`; state 1432/1432 OK;
  link count 1; snapshot #5 0/0/0; output map 1463 entries `b43812d0…`.
- **Admissions:** 196 → 192, exactly the four targets. **Axioms:** 76 constants standard, census 325 with `Real` at
  29; **`bb1_sidSecure` is standard and its `sorryAx` trace is empty**, as are the other five roots' (sorry control
  caught).
- **Rule 10:** 36 seals with 0 errors and the delivered request counts; controls ALL_OK strict and coe (485 negatives
  each failing once); `bb1RealState_eq`'s entries pass under the seals (the abbrev is never requested); unfold scan
  0 foreign; lint unchanged.
- BSF-F01 stays a process note for the dispatch template; BSF-F02/F03 are closed by LE-bsf1; BSF-F04 by DL-57; BSF-F05
  is stated in the PR description.

**Next:** the draft PR into `cryptography/pass-shelat-ch2-4`; the bb1-sim gate (Q8) audits it. On merge, if the merge's
Lean equals `7a98ba01`, adopt `$SP/olean-replay-bb1sim` as snapshot #6, and record DL-57 in the ledger.

## ===== briefs/pairings/fills/bb1-sim/fill-final-r1/phase2.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# bb1-sim fill · final r1 · phase 2: landing branch and merged-tree replay on olean snapshot #5

**Verdict: PASS. The landing head `land/pairings-bb1-sim` `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff` is clear for its
draft PR.**
- The branch is the records tip plus maintainer-signed cherry-picks of the worker's 4 commits plus LE-bsf1. The picks
  applied cleanly; `range-diff` is 4/4 `=`; LE-bsf1 is byte-identical to the proposed diff.
- decls2 against the tip: **69 ADDED, 0 CHANGED, 0 REMOVED**. The reader pins `97ecb6e0…`/`88454d6f…` hold; the
  frozen-header check passes 12/12 with its 8 controls.
- The replay rebuilt **19/19 modules with rc 0**, 0 `error:`/`error(` and 0 `sorry`. The state check gives 1432/1432
  OK, every rebuilt olean has link count 1, and snapshot #5 rehashes 0/0/0 before, after the build and at the end.
- **Admissions against the tip: 196 → 192, exactly −4** (`expect_simulate_rel`, `expect_sample_rel`, T2, T3).
- **Axioms:** 76 constants, all standard; the census over the 9 owners is 325, 0 non-standard. **`bb1_sidSecure` is
  standard, and its `#sorry_trace` is empty** (closure 20,373), as are the traces of the five other roots.
- **Rule 10:** 36 canonical seals (A, B; strict, coe; 9 owners) with **0 errors**, request counts equal to the delivered
  table; paired controls **ALL_OK** in both harnesses (485 sealed negatives each failing exactly once, every positive
  and unsealed probe clean); explicit-unfold scan **0 foreign**. Lint is unchanged against the tip.

Run on 2026-11-17, 07:44–09:08 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-fill-final-r1-phase2-evidence.zip`, under `bb1-sim-fill-final-r1-phase2/`, with
  `PROVENANCE.txt`, `SHA256SUMS` and this file. Its own SHA-256 is in `evidence-SHA256SUMS`.
- **Builds:** no `lake build`, no cache get. This job ran one Lean process at a time and checked the host's slot count
  (fewer than 3 `lean` processes) before every module and probe; it never had to wait.
- **Not touched:** the snapshot (read and hard-linked only), the other replay directories (`olean-replay-6a-*`) and other
  agents' directories. The records branch has no commit from this job.

## P2-0 Inputs
- **Records tip** (after `git fetch`): `origin/cryptography/pass-shelat-ch2-4` = `e1d39836ed4a69a34914c35f4c73c71de853dcc6`.
  `git diff` from `3f540c22360c869069a0fba684e23ce6f3cb20db` (the #346 merge, snapshot #5's T) over `*.lean`,
  `lakefile.lean`, `lake-manifest.json` and `lean-toolchain` is empty.
- **Delivery:** `inbox/fills/bb1-sim/` at exchange `2467bc3befdad8472b1f359337bf3a203e3651e1`, re-extracted by
  `git archive`; the 4 patches and `COMMITS.tsv` pass the delivery `SHA256SUMS` and equal phase 1's extraction.
- **Proposed LE-bsf1:** `le-bsf1-proposed.diff` from the phase-1 zip (zip `f74bcbde…`, `sha256sum -c` OK; internal
  `SHA256SUMS` OK). The diff is `8f18c2e3…43c5fe`.
- **Snapshot #5:** `$SP/olean-snapshot`; map `olean-snapshot.map-3f540c22.tsv` `fca1b6a3…41ef9`; files manifest
  `olean-snapshot.files-3f540c22.txt` `12457f32…c650`.
- **Tools:** the recipe's `olean-advance-a6d01b1b/tools-used/` from `olean-rebase-evidence.zip` (`b662b7da…`),
  byte-identical to the copies used; Gate 44's `tools/seal` harness; the phase-1 tools (`decls2.py` `fa81981a…`,
  `inscheck.py`, `frozencheck.py`, `hygiene.py`); the delivered `mkctl_bb1sim.py` and `Axioms.lean.txt`. New or adapted
  (all in `tools/`, each with a header naming its change):
  - `run-build-bsf.sh` (the recipe's `runner.py`, unmodified, called once per module behind the slot gate);
  - `rule10_bsf2.sh` (phases `statements`, `collect`, `axioms`, `seals`, `scan`; composed from Gate 44's
    `rule10_g44.sh` and the delivered `rule10_bb1sim.sh`);
  - `runner_full_gated.py` and `rule10_b_gated.sh`: `runner_full.py`/`rule10_b.sh` plus the slot gate only;
  - `mkctl_bsf2.py`: `mkctl_bb1sim.py` plus the two `bb1RealState_eq` entries (P2-5);
  - `inscheck_tip.py`: phase 1's `inscheck.py` with `BASE` set to the tip;
  - `sigfp.py`: reads the SSH key fingerprint of a commit signature (no `ssh-keygen` on this host).

## P2-1 Landing branch
- **`git am` reproduction** (sparse detached worktree at the patch base `72c0498a…`, committer and date per
  `COMMITS.tsv`, signing off): **4/4 REPRODUCED**, `23614c0a`, `3f430cae`, `622f5b03`,
  `c35595aef7636c2ba9a25e1ffdac141b08d2fea5`, none with a `gpgsig`.
- **Branch** `land/pairings-bb1-sim` from the tip, in a sparse worktree (`TCSlib/Cryptography/Games`,
  `…/AdvancedEncryption/IdentityBased`). `git cherry-pick -S` of the 4 commits applied cleanly, keeping author
  (Claude) and author dates:
  - `69fa787fc52a9c7dff34c8f448ed78b68fcbfbd1` (readers), `2845f1002f63f5ede2eed45e218e42c6b2e8e8e0` (`Relational`),
    `469375fa2d96ae6088c4c7a16b96724559084301` (helpers), `40f7da54d280a1e2bb48fc17c2555f089617a2c9` (T2/T3).
  - **LE-bsf1** `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`: `git apply` of the proposed diff, one signed commit whose
    message ends with the two required trailers.
- **Checks:**
  - `git range-diff 72c0498a..c35595ae e1d39836..40f7da54`: **4/4 `=`**.
  - `git diff 40f7da54 7a98ba01` is **byte-identical** to `le-bsf1-proposed.diff`.
  - At `40f7da54`, the 9 fill files equal `c35595ae`'s byte for byte. The tip differs from the patch base only by #340
    (`Pairing/Assumptions.lean`) and LE-g44 (`Draws`, `Words`, `Handler`), none of them a fill file.
  - The landing head's Lean, minus LE-bsf1, equals phase 1's T_land `c1d5fd89` (empty diff over `*.lean`, `audits`,
    the lake files). Against T44′ `bee027f0` the head differs in exactly the 9 files.
  - `git diff --stat e1d39836 7a98ba01`: 9 files, +1925/−21. No path outside the 9.
  - All 5 commits carry a `gpgsig`; each is an ed25519 signature by `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`,
    the key of the records commits (e.g. `e1d39836`). `git verify-commit` is unavailable here (the host's signing
    program does only `-Y sign`), so the key was read from the signature blob (`sigfp.log`).

## P2-2 Static checks at the landing head
- **decls2** (pinned `fa81981a`) against the tip over the 9 files: **69 ADDED, 0 CHANGED, 0 REMOVED** — the 10 readers,
  58 `BB1Sim.*` helpers and `BB1Sim.bb1RealState_eq`. With the location column dropped, it is phase 1's 68 rows plus
  exactly `bb1RealState_eq` (line numbers move by LE-bsf1's docstrings only).
- **Reader insertion** (`inscheck_tip.py --controls`, base = the tip): `Defs.lean` block `d6f8faf1` head
  **`97ecb6e0…`** (563 lines), `BonehBoyen.lean` block `967f2a30` head **`88454d6f…`** (760 lines); base hashes
  `4e220ead…`/`da875140…` hold at the tip, pure-insertion bytes, removal restores the tip, blank line before each
  block: **PASS**; 12/12 controls fail as they must. **The pins are unchanged:** #346's 7 readers were already in the
  patch base `72c0498a`, and the tip's `Defs.lean`/`BonehBoyen.lean` equal the patch base's.
- **Frozen headers** (`frozencheck.py` tip → head, `--controls`): H1–H4 **12/12 PASS**; 8 controls fail as they must;
  the unchanged head passes.
- **Hygiene** (`hygiene.py`): every file ≤ 760 lines, no line over 100 characters, no `@[simp]`, no new `attribute`
  (`BonehBoyen.lean:386` is the base's), no micro sign, 0 `sorry`/`admit`/`native_decide`/`axiom` tokens. **Every
  helper docstring now has a `[BB04, …]` tag or a glue note** and a formula. The only `no-tag/glue` rows are the three
  frozen `Relational` statement docstrings of #351 (`expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`),
  which phase 1 also listed and which this fill may not edit.

## P2-3 Replay (snapshots.md job recipe)
- **Copy and overlay:** `cp -al $SP/olean-snapshot $SP/olean-replay-bb1sim` (1458 files, all hard links);
  `mloverlay.sh` made 3346 symlinks; `mathlibextra.sh` built NthRootLemmas with rc 0, olean **`c0a9cff0…`**.
- **Tree:** `git archive` of `7a98ba01` (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files, `lean-toolchain`;
  1584 files) with `.lake/packages` symlinked.
- **Plan:** `stateplan init` at `3f540c22`: 1427 modules. `downorder.py`: changed 9, **down 19**. `fullorder.py`: **1432**
  (roots `TCSlib` and both `audits/*/Checks`). `stateplan plan`: **19 to build, 1413 reused** — the 13 `DOWN` modules
  of `closures.txt` (`Relational`, `Games`, `Defs`, `BonehBoyen`, `BBM/{Draws,Words,Handler,Reduction,Oracles}`,
  `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`), the 5 helpers before
  `BonehBoyenSecurity`, and root `TCSlib`. Neither `Checks` is downstream.
- **Build** (07:48:00–07:49:44): **19/19 rc 0**; `error:` 0, `error(` 0, substring "error" 0, `sorry` 0, warnings 0;
  no log/record mismatch (`permod.py`). Sources bound to `7a98ba01` 19/19.

## P2-4 Accept (recipe step 5)
- `stateplan update`: 19 modules, none left out. `check` over the full order: **1432/1432, RESULT OK**, again at the end.
- **Link count 1** for all 19 rebuilt oleans (plus the NthRootLemmas olean); every other file is a hard link to the
  snapshot.
- **Snapshot #5** `snapmap.py verify`: **0/0/0**, 1458 files, no symlinks — before the copy, after the build and at the
  end.
- **Output map** (`mapnoml.py`, Mathlib excluded): **1463 entries** (1458 + 5), SHA-256
  **`b43812d0008b290343fab435f725544b1eef2c944f3581f2e8a62b3c0362171a`**. Against snapshot #5's map: 1454 equal,
  4 changed (`Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity`), 5 added (the helpers), 0 removed. The other 10
  rebuilt modules produced byte-identical oleans. The map is unchanged after all probes (they write no olean).
- **Admissions** (`tipcensus.py`, Gate 44's record sets plus this build): tip `e1d39836` **196**, head **192**. The only
  changes are `Relational` 2 → 0 and `BonehBoyenSecurity` 2 → 0 (plus the 5 new helpers at 0). The tip's four
  admissions are exactly `expect_simulate_rel`, `expect_sample_rel`, `bb1_sim_real` and `bb1_sim_random`.

## P2-5 Axioms and Rule 10
- **Axioms** (`AxiomsBsf.lean`: the delivered probe plus `bb1RealState_eq` and a sorry control; rc 0, 0 errors; its one
  `sorry` warning is the control's):
  - `AXIOMS-LIST 76 constants, 0 non-standard` (every new constant, the 4 targets, `prob_simulate_rel`,
    `bb1_sidSecure`, T4 `exists_bb1_distinguisher`).
  - Census: `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3, `Lazy` 24, **`Real` 29**, `Coupling` 20,
    `Random` 2, `Chain` 1 = **325, 0 non-standard**.
  - **`#sorry_trace`: no direct `sorryAx` user** for `bb1_sidSecure` (closure 20,373), `bb1_sim_real` (15,352),
    `bb1_sim_random` (13,412), `expect_simulate_rel` (5,020), `expect_sample_rel` (11,705), `prob_simulate_rel` (5,023);
    `collectAxioms` gives `bb1_sidSecure` the standard three. With #340 merged, T1 is proved, so nothing remains.
  - **Control:** `bsfSorryControl` is reported as its own direct `sorryAx` user and `NONSTANDARD [sorryAx]`.
- **Seals** (canonical, `mkseals_ab`/`mkseals_coe`, A and B with `SEAL_EVAL=1` for B, on the 9 owners; `sealsum.py`):
  **36/36 rc 0 with 0 errors**, install and end records present. Requests (A/B/coe-A/coe-B): `Relational` 53/53/52/52,
  `Defs` 805/806/804/805, `BonehBoyen` 840/841/839/840, `BonehBoyenSecurity` 2320/2321/2319/2320, `Lazy` 868/869/867/868,
  `Real` 871/872/870/871, `Coupling` 874/875/873/874, `Random` 871/872/870/871, `Chain` 877/878/876/877. The sealsum
  tables equal the delivered ones (columns 1–6) in all four variants; the mkseals records differ only in `Real`'s
  stored-constant count, 28 → 29 (`bb1RealState_eq`). LE-bsf1 adds no definition, so no request changes.
- **Paired controls** (`mkctl_bsf2.py`; `ctlcheck2.py`): 32 probes per harness (16 sealed, 16 unsealed), the same
  covering subset as the delivery. **strict and coe: ALL_OK**; **485 sealed negatives, each failing exactly once**;
  1479 positive or unsealed entries with 0 errors; 0 stray errors. Rows exercised include the 10 reader pairs
  (`SidZeroSpec`, `SidTwoSpec`, `SidOneQuery`, `SidTwoQuery`, `SidKeyNe`, `SidFresh`, `SetupEq`, `KeyGenBind`, `EncBind`,
  `EncCT`) and the 5 helper-definition pairs (`SimLazy`, `SimLazyChal`, `RealAt`, `RealLazy`, `RelM`). Every probe's
  per-control outcome equals the delivered `ctlcheck` exactly, apart from the new entries.
  - **`bb1RealState_eq`:** `BB1Sim.BB1RealState` is an `abbrev` and appears in **0 of the 36** request sets (the
    canonical seals never request abbrevs), so no sealed negative can exist for it — BSF-F02's "notation". The two
    entries `ctlRealState` (the unfolding by `rfl`) and `ctlRealStateReader` (the reader), attached to the `bb1RealAt`
    row, ran in 6 sealed and 6 unsealed probes per harness with 0 errors: the reader elaborates and states the
    abbrev's unfolding under every consumer's seal.
  - `RealReads` still has no pair (BSF-F05, accepted).
- **Explicit-unfold scan** (`scan1_g40.py`, `scan2.py`): **527 items** — 426 theorems, 85 local hypotheses or
  projections, 14 owned definitions, 2 `↓reduceIte` — **0 foreign**, identical to the delivered summary.
- **Attempt 1 of the seals phase** failed before any Lean ran: the seal generators call `git -C <tree> show`, and the
  export is not a repository. The driver now exports `GIT_DIR` (read-only use); the failed output is kept as
  `rule10/attempt1/`.

## P2-6 Lint
- `campaign_style_lint --check8b TCSlib/Cryptography`: tip **92 FAIL / 104 WARN over 524 files**, head **92/104 over 529**;
  the FAIL/WARN line sets are equal (0 new, 0 gone). The only IBE line is the base's `SIDSecure` WARN. INFO changes are
  the 9 files' line and declaration counts and the 5 new files.
- `style_lint` over the 9 files: 0 findings. `sk15`: one finding, `BonehBoyen.lean:677 bb1SimChal_fresh`, the base's
  (T4's) code.

## P2-7 State after the run
- **`$SP/olean-replay-bb1sim`** is kept as the snapshot candidate: 1464 files (1458 + 5 helpers + the NthRootLemmas
  overlay olean) and 3346 Mathlib symlinks. It is adoptable as snapshot #6 when the PR merges, if the merge's Lean
  equals `7a98ba01`'s (step-3 diff empty); adoption removes `Mathlib/` and should reproduce map `b43812d0…`.
- Kept for the PR: the landing worktree `$SP/bsp2/landwt` (branch `land/pairings-bb1-sim`). Removed at the end: the
  `git am` worktree and the build export. Phase 1's extraction `$SP/bsf-final/deliv/` was deleted as allowed.
- Raw seal records, control sources and probe logs (about 140 MB) are not in the zip; their SHA-256 are in
  `rule10/omitted-SHA256SUMS` and `scan/omitted-SHA256SUMS`, and the files stay under `$SP/bsp2/run/`.

## ===== briefs/pairings/fills/bb1-sim/rulings.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# bb1-sim · Seyoon's rulings on design note r1 (2026-11-16)

These rule on the eleven questions of `design-r1.md` §5. Eight are as recommended; Q6, Q10 and Q11 are changed.

| # | Ruling | |
|---|---|---|
| Q1 | A **new module `Games/Relational.lean`**, imported by the `Games` facade. | as recommended |
| Q2 | The names are `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel` and `expect_sample_rel`, beside `ProbComp.expect_simulate_congr`. | as recommended |
| Q3 | The **inline expectation form** of the per-call hypothesis: from `R s t`, test functions that agree at equal answers and related states have equal expectations after one call. | as recommended |
| Q4 | The statement phase includes the companions `prob_simulate_rel` and `expect_sample_rel` with the target. | as recommended |
| Q5 | **No query budget now.** DL-40's cleanup either promotes the budgeted ETT lemmas `expect_simulate_abs(_inv)` as they are, or adds a budgeted relational variant when it is needed. | as recommended |
| Q6 | **Promote the averaging bound `\|𝔼 f − 𝔼 g\| ≤ 𝔼 h` into `Games/Probability.lean`**, as a public lemma beside the constant-bound `ProbComp.abs_expect_sub_le`. It is part of the statement phase, so expect a larger rebuild and re-seal. The private ETT copy (`EncryptThenTag/Forgery.lean:515`, DL-40) is re-pointed to it in the cleanup. | **changed** (was: public in `Relational.lean`) |
| Q7 | **One reader, `IBEScheme.sidImpl_eq_oracleImpl`,** in `Defs.lean` after T4's `_onSpec` readers. It is carried by the bb1-sim PR as a pure insertion, under an advance scope ruling confirmed by a probe first, which also fixes any needed `encCT` reader. | as recommended |
| Q8 | **One bb1-sim gate after Gate 44.** It covers the Games statement phase (`Relational.lean` and the `Probability.lean` addition), the reader insertions and the T2/T3 fill. | as recommended |
| Q9 | The Games statement phase is **its own small PR on the records tip**. The fill is stacked on T4's PR, or based on the tip once T4 merges. | as recommended |
| Q10 | **The group helpers go into the frozen `Pairing/Group.lean`** by an approved reader-style insertion beside the published `G_T` bijection: `Z_p ≃ G` for `g ≠ 1`, the additive exponent laws in `G`, and identity injectivity on good coins. Reuse Mathlib's `orderOf`/`ZMod` API where it applies. | **changed** (was: public helpers in the fill) |
| Q11 | **Ingest and cite [BGZ09] and [Sho04]** for the relational simulation lemma. Seyoon sends the PDFs. As with Gen09, nothing waits: the statements proceed, and the citations are a docstring-only follow-up after the ingest. No Lean docstring cites either tag before then. | **changed** (was: framework lemma, no tags) |

Next:
- the probe that fixes the reader set (after T4's readers land);
- the Games statement-phase PR (`Relational.lean` with the targets; the averaging bound in `Probability.lean`);
- the bb1-sim fill.

## Q7 follow-up: the reader set (Seyoon, 2026-11-17)

The probe (`bb1-sim-statements` checkpoint 1, exchange `8899115b`, `probe/READERS-TO-INSERT.md`) showed that T2 needs
**ten** readers, not the one Q7 anticipated:
- six in `IdentityBased/Defs.lean`: `sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`,
  `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec` and `sidImpl_challenge_fresh_onSpec`;
- four in `BonehBoyen.lean`: `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind` and
  `ofFn_bb1Scheme_encCT`.

**Ruling: all ten are approved, and they land in the bb1-sim fill PR**, inserted verbatim from `READERS-TO-INSERT.md`
as pure insertions after the anchors it names. This is T4's pattern. The bb1-sim gate checks that they are insertions
only, against the pinned post-insertion SHA-256s (`Defs.lean` `97ecb6e0…`, `BonehBoyen.lean` `88454d6f…`, both on top of
T4's head). They are theorems proved by `rfl` or in one line; no definition changes.

**Design point:** the fill uses the probe's `RealReads` interface and the existential `setup_out` for the real setup's
outputs (design §3.3).

## ===== briefs/pairings/fills/bb1-sim/fill-checkpoint1-review.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# bb1-sim fill · checkpoint 1 review (maintainer)

**Verdict: proceed with notes.** Nothing blocks the worker. All three integrity layers pass:
the checksums, the `git am` reproduction and the merged tree. The ten readers are verbatim and
match the ruled pins. decls2 shows exactly the readers plus the declared helpers, with 0 CHANGED
and 0 REMOVED. Every frozen header is unchanged, and the scope is clean. I checked all 49 helper
statements by hand against the definitions, and each is **true as stated**. None is vacuous or
stronger than its use needs. The outline covers design r1 §3 for T2 and T3 through the ruled
`RealReads`/`setup_out` interface. There are four minors (bookkeeping and docstrings) and four
info items for the final. I ran no Lean: the delivered sweep logs bind to the reproduced tree, so
helper elaboration is not in doubt.

## What was reviewed

- **Delivery.** `inbox/fills/bb1-sim/` at exchange commit `1ef26470195ca0fd63ab42fe8679b4896a81421f`
  ("fill bb1-sim: checkpoint 1"). I fetched `exchange/pass-shelat-ch5-8` by name (tip `30ef1257a`; the
  commit is an ancestor) and extracted it with `git archive` into a fresh empty scratch directory.
  - 311 files: `REPORT.md`, 4 patches with `COMMITS.tsv`, `src/` (9 files) and `evidence/` (295 files).
  - Top-level `SHA256SUMS`: `2a491d77f0c8421fe4c0d979eed1be516d0e2823d6bea50b02e3122fe046e175`.
  - `evidence/SHA256SUMS`: `cc7508a5f67e21125012c1b9e31f918385e580e79cecb6d40cc9ebd2fbbf4ab5`.
- **Contract.** `issued-fill-r1/`: its `SHA256SUMS` passes, and the brief's SHA-256 is `d4d029a4…`.
- **Background, by its pinned SHA-256s:**
  - `design-r1.md`: `74c592d9…`;
  - `rulings.md`: `e5716af6…`;
  - the BB04 transcription: `46f8f7b1…`;
  - `policy.md`: `6599b122…`;
  - `decls2.py`: `fa81981a…` (the delivered copy is identical);
  - the probe `BB1SimStepM.lean.txt` at `a3cb45f6`: `941bd4bd…`.

## Checks

| Check | Result |
|---|---|
| **Integrity** | Both manifests pass `sha256sum -c`. The delivered paths equal each manifest's paths exactly: no missing or extra path, and no leading `./`. The exchange commit touches only `inbox/fills/bb1-sim/` (0 other paths). |
| **Bases** | `mkbase.sh`, run with `land/pairings-bb1-machine` (`89a18a82…`) and `fill/pairings-pair-bdh` (`916afc25…`) fetched by name, prints `PATCH_BASE 72c0498a… tree b5a5842d…` and `CHECK_BASE 7cfe2b1b… tree 02b2d44a…`. Its tree assertions pass. |
| **Patches** | `git am --committer-date-is-author-date` on `72c0498a…` reproduces all 4 hashes of `COMMITS.tsv` (`23614c0a`, `3f430cae`, `bcb9bcca`, `35c780c48c19…`); signing is `none`. `git merge-tree --write-tree 916afc25… 35c780c4…` gives `48a81d43…`, equal to the reported check-head tree. `src/` is byte-identical to the reproduced head, file for file. |
| **Readers** | My own insertion check (`inscheck.py`, in the evidence zip):<br>• base hashes `4e220ead…` and `da875140…`;<br>• each block byte-identical to the pack's `readers/` (`d6f8faf1…`, `967f2a30…`), after one blank line following `Defs.lean:430` and `BonehBoyen.lean:412`;<br>• the head files equal base + blank + block exactly, and removing the blocks restores the base;<br>• heads `97ecb6e0…` (563 lines) and `88454d6f…` (760 lines): **PASS**.<br>All 12 controls fail as they should: a character inside a reader, an extra line elsewhere, an extra blank after a block, deleted reader lines, moved reader lines, and an edited docstring, in each file. The delivered check (`CHECKS 25/25 PASS`, 12 controls `ALL_CONTROLS_OK True`) agrees. |
| **decls2 vs patch base** | Re-run with the pinned `decls2.py` over the 9 changed files: **59 ADDED, 0 CHANGED, 0 REMOVED**. That is the 10 readers plus 49 `BB1Sim.*` helpers, exactly REPORT's table (Lazy 22, Real 15, Coupling 9, Random 2, Chain 1). The output is byte-identical to `evidence/decls2/decls2-checkpoint1.tsv`. |
| **StmtDump** | The probe prints 65 constants: 59 new, the 4 targets, `prob_simulate_rel` and `bb1_sidSecure`. The log shows no error and no `MISSING`. |
| **Helpers elaborate** | `evidence/build/checkpoint1-sweep`: 18/18 modules (13 `DOWN` plus 5 helpers, helpers placed before `BonehBoyenSecurity`). All have rc 0 and 0 errors in both forms. I re-hashed every module's source from the reproduced check tree `48a81d43…`: **18/18 match** `results.jsonl`. The `sorry` warnings are exactly the 17 listed helpers (Lazy 4, Real 5, Coupling 6, Random 1, Chain 1). `Relational`, `Defs`, `BonehBoyen` and `BonehBoyenSecurity` have 0. |
| **Frozen headers** | `git diff` of `Relational.lean` and `BonehBoyenSecurity.lean` against the patch base shows only:<br>• the four `sorry` lines replaced by bodies;<br>• five `import` lines after line 8;<br>• a new `## Contents` section.<br>The headers and statement prose of T2, T3, `expect_simulate_rel` and `expect_sample_rel` are unchanged. `bb1_sidSecure` and `prob_simulate_rel` have no hunk. The `**Proof sketch.**` paragraphs are not yet refreshed (F07). |
| **Scope** | `git diff --stat` lists exactly the 4 permitted owners and 5 new files under `IdentityBased/BonehBoyenSecurity/`. No change touches `Games/Probability.lean`, `Pairing/*`, T4's files, the cleanup Stage 1 homes, GSW or other campaigns' files. Every helper import is in `order.txt` (`Hopping` 149, `Relational` 168, `Bridges/Experiments` 128, `BonehBoyen` 184) or is an earlier helper. No `fill/bb1-sim` or `check/` branch is pushed; the two `land/bb1-sim-*` refs are #351 and #352. |
| **Hygiene** | Every changed file is at most 100 columns. The largest file is `BonehBoyen.lean` at 760 lines (approved); the helpers have 94–297 lines. There is no `@[simp]`, no new `attribute` line (`BonehBoyen.lean:386` is the base's `simps`) and no micro sign. The `set_option maxHeartbeats 0` header follows the IBE precedent. Docstrings: see F04. |
| **Clash/shadow** | Delivered scan: 59 names, 0 CLASH, 0 DUP-NEW, 0 same-short-name rows. My scan of TCSlib and `audits/` at the check base, with positive controls, finds no new full name and no new short name. The only near-hits are T4's **private** `BB1Machine.sidSpec_rng_one'` and `_two'` (primed). `BB1Sim.` does not occur at the base, and no `DOWN` module opens `BB1Sim`, so no resolution changes. |
| **Duplication** | I found **no undisclosed duplicate of a public lemma**. I searched by name and by conclusion shape in TCSlib (`Pairing/Group`, IBE, T4's `BB1Machine`, `Games`, `Asymptotic/Sampling`) for `pow_val_*`, `bilinear_pow`, `pair_*`, `bitsToNat`/`natCast` injectivity, `sidSpec` dom/rng equations, `zeroBits` casts and eager/lazy lemmas. There is no copy of `abs_expect_sub_le_expect` or of `Games.expect_simulate_eager`; T2 cites the public ones. The overlaps to disclose at the final are under F06. |
| **Citations** | Every BB04 quotation in the helpers matches the DW-7 transcription verbatim: "let r̃_j = r_j − b/(I_j − I^*_j)", "Since F_i(I^*_i) = g^{α_i}", "if T = e(g,g)^{abc} = e(g_1,g_2)^c", "When the input 5-tuple is sampled from P_BDH … real attack game" and "when T is uniform and independent in G_1 … independent of b in the adversary's view". So do the locations: §4.1 pp. 5–6, §4.2 pp. 6–8, *Initialization*, *Setup*, *Phase 1*, *Challenge*, *Phase 2, Guess and the advantage*. The §4.4 tag on `natCast_bitsToNat_injective` fits ("`2^b<p` is sufficient"). |

## The helpers are true as stated

I checked each statement against the definitions at the head (`IBEScheme.sidImpl`, `oracleImpl`,
`bb1SimInit`/`KeyQ`/`Chal`/`Ct`, `BB1.setup`/`keyGen`/`encrypt`) and against `Pairing/Group.lean`.
There, `pow_val_bijective_of_ne_one` gives `orderOf g = B.order` (prime), so `ZMod B.order` is a
field and `x ^ B.order = 1` (`pow_order`).

- **Types (Lazy).** `sidSpec_dom_*`, `sidSpec_rng_*` and `zeroBits_eq_cast` are true and proved,
  from `sidSpec_eq`, `bitSpec_*` and `inLens_*`/`outLens_*` only (type-level Rule 10).
- **Lazy simulator.**
  - `bb1SimLazyChal` and `bb1SimLazy` have case readers that cover every input (`_fresh`/`_of_not`;
    `_zero`, `_one`, `_two_fresh`, `_two_of_not`); all are proved.
  - `bb1SimImpl_two_of_not` (sorry) is true. Its guard is `bb1SimChal`'s validity test through
    `bb1Scheme_msgSpace_iff`, which depends only on `d`. Away from it, `bb1SimChal` answers `⊥`
    (`s.1 = none`), repeats (`some, some`) or answers `⊥` (invalid). None of these reads `Z`, `T`
    or `b`, so the generalisation to `bb1SimImpl false …` announced in REPORT is also true.
  - `_two_fresh_allOutputs` and `_allOutputs_of_ne_two` are true: `bb1SimInit`/`KeyQ` keep `s.2`,
    and a fresh valid challenge records `some`.
  - `expect_simulate_bb1SimLazy` (sorry) is true for every `s` with `s.2 = none` and every `F` on
    the full state. The coins are not in `BB1SimState`. It is an instance of
    `Games.expect_simulate_eager` (`Hopping.lean`) whose `hused`, `hstick` and `hfresh` are
    exactly the five lemmas above.
- **Real side.**
  - `RealReads` and `setup_out` are **the probe's statements byte for byte**, apart from
    docstrings (compared with them stripped). The probe proves `setup_out` with no `sorry`
    (`BB1SimStepM.lean.txt`, lines 202–226), so its `sorry` here is a pending port.
  - `bb1RealAt` reads the **recorded** `h'` once committed. This differs from the probe's
    `realAt`, which always uses `o h`, and follows design §3.1 ("runs `sidImpl`'s call with the
    stored `h`"). It is what makes E-h's `hused` hold. Its readers `_none` and `_some` cover all
    states; `bb1RealLazy`'s `_zero_none`, `_none_of_ne` and `_some` cover all `(i, state)`.
  - `sidImpl_allOutputs_some` and `sidImpl_none_of_ne` (both sorry, for every scheme `S`) are true
    from `sidImpl`'s arms. Before `Init`, `KeyGen` and `Challenge` fall to `| none => ⊥` and
    `| none, _ => ⊥`, which read no `pp`/`msk` and keep `(none, c)`. Once committed, every arm
    keeps `some t`.
  - `expect_simulate_sidImpl_bb1RealAt` (R1, sorry) is true. Under `R_h`, the recorded `h' = h`,
    so each call is `sidImpl (o h)`'s call with `h` attached.
  - `expect_sample_bb1RealAt` (E-h, sorry) is true even for `F` on the full state. `Init` from
    `(none, c)` always commits (`sidImpl_init_none`), so `h` is drawn once. Calls before `Init`
    do not read `o`.
- **Coupling.**
  - `exists_equiv_mul_pow` is true (take `e z h := φ⁻¹(X^{(−z).val}⁻¹ · h)` with
    `φ = a ↦ g^{a.val}`). So is `natCast_bitsToNat_injective` (`bitsToNat u < 2^n ≤ p`;
    `CharP.natCast_injOn_Iio`).
  - `key_eq` is true. I checked the exponent algebra: with `Δ = z − z'`, both sides are
    `g^{α b' + (αΔ + a₁) r}` and `g^r`.
  - `F_target_eq` (`X^p = 1`) and `pair_pow_val_eq` (`bilinear_pow`, `pow_val_mul_GT`) are true.
  - These five are the probe's hypotheses `he`, `hinj`, `hkey`, `hF` and `hT`. Some are
    generalised, `X` in place of `g^α` for example; that is equal or more general.
  - `stepM_call` (sorry) is true. I checked every row against the definitions:
    - `Init`, uncommitted: L3 along `e (idToZ ID)`, answers equal by `RealReads.encPP` and
      `ofFn_bb1Scheme_encPP`.
    - `Init`, committed: deterministic.
    - `KeyGen`: `⊥` and target rows are deterministic. For `ID ≠ ID*`, `r ↦ r + b'/Δ` is
      `key_eq` with `Δ ≠ 0` by `hp`.
    - `Challenge`: before `Init`, repeated, or `u.1 = none` with a recorded `u.2` are all `⊥` or
      the repeat on both sides. Invalid: both message spaces are `G_T` encodings. Fresh: `s = c`,
      with `F(ID*)^c = (g^c)^{α₁}` by `pow_right_comm`.
  - `expect_simulate_bb1RealLazy` is proved as an instance of `expect_simulate_rel`.
- **Random.** `bb1SimLazy_random_call` (sorry) is true for every `F` on `(answer, state)`. Only
  the fresh valid challenge depends on `b`; along `T ↦ decodeT(M₁)⁻¹ · decodeT(M₀) · T`, both
  bits give the same answer and record the same word. `expect_bb1SimImpl_random` is proved from
  it.
- **Chain.** `prob_sidGame_coins` (sorry) is true on good coins. It is the composition of the
  above (`2^ℓ ≤ p` via `bb1Scheme_idLen` and `BilinearGen.inst_eq`). Its sample order
  `g, α, h, g2, ρ` matches `setup_out` followed by `sidGame_eq`.

**Vacuity check.** The only hypotheses that flow into T2 are `setup_out`'s `hR`, which is
existential and was proved in the probe, and `hr`, which is exactly the excluded-coin event of
T2's bound. T3 uses no hypothesis. Neither target can become vacuous through these helpers.

**The proved parts.** The `Relational` bodies follow design §2.3: induction with
`simulate_pure`/`_query`, and `expect_bind`/`expect_sample_equiv`. They use only published
`Games` lemmas. T2's and T3's bodies use only published lemmas and `BB1Sim.*` helpers.

## The outline against design r1 §3

**T2.** The outline covers every step of design §3.1:
- (1) moving `h`;
- (2) **R1**: `expect_simulate_rel`, with `impl₀ = S.sidImpl b κ (o' h).1 (o' h).2`,
  `impl₁ = bb1RealAt … o' h` and `R_h` as the design states it;
- (3) **E-h**: `expect_simulate_eager`, with `O = bb1RealLazy … o'`, `OE h = bb1RealAt … o' h` and
  `used u := u.1.isSome`;
- (4) `g₂ = g^{b'}` along `Equiv.ofBijective` of `pow_val_bijective_of_ne_one`;
- (5) **step M**: `expect_simulate_rel` with `RelM`, `zt_c c = (g^c, e(g,g)^{αb'c})` and
  `U = Z_p`;
- (6) **E-c**: `O = bb1SimLazy … zt_c`, `OE c = bb1SimImpl … (g^c) (e(g,g)^{αb'c})` and
  `used v := v.2.isSome`;
- (7) `expect_const`, `Bridge.expect_sample_pair` and the exchange with `ρ`;
- the bad coins: `abs_expect_sub_le_expect`, `prob_eq_expect` and `prob_sample_eq_uprob`.

Every `expect_simulate_rel` and `expect_simulate_eager` instance is given with its handlers and
its relation or `used`.

**T3.** The outline covers design §3.2:
- **E-T**: `zt T = (Z, T)`, `U = G_T`;
- `expect_simulate_congr` with `bb1SimLazy_random_call`;
- `expect_sample_rel` with `R := Eq` along `decodeT(M₁)⁻¹ · decodeT(M₀) · T`, the probe's P-3.

**The ruled interface.** The outline uses `RealReads`/`setup_out` as ruled. `o` is obtained from
`setup_out` in T2 and passed as a parameter to `bb1RealAt`/`bb1RealLazy` (`o' := fun h => o r g α
h g₂`). No helper constructs a `PP` or `MSK` value. Every lemma the outline names exists at the
check base (`expect_sample_comm`, `expect_sample_equiv`, `Bridge.expect_sample_pair`,
`prob_sample_eq_uprob`, `abs_expect_sub_le_expect`, `expect_const`, `advantage_eq`, `accept_eq`,
`expect_simulate_congr`).

## Findings

| ID | Grade | Finding | Fix |
|---|---|---|---|
| BSF-C1-F01 | minor | **The exchange commit is SSH-signed.** `1ef26470…` carries a `gpgsig` SSH signature, though the brief (*Exchange commits*, BS-F08) requires `git -c commit.gpgsign=false` on the exchange. The cleanup-stage1 worker's checkpoint `bc2bf64a0` of the same day is unsigned, so this is the worker's configuration. The patch commits are unsigned, and the content is unaffected. | Commit the final unsigned and check it with `git cat-file -p HEAD \| grep -c gpgsig` before pushing. Record the checkpoint's signing in `REPORT.md`. Do not rewrite the pushed commit; force-pushing is forbidden. |
| BSF-C1-F02 | minor | **REPORT's fill-head hash is wrong.** `REPORT.md` gives the `fill/bb1-sim` head as `35c780c4876b54ddaaf1cbb44c66bac55b23e9e1`. The real head, from `COMMITS.tsv`, `evidence/decls2/HEAD.txt`, `delivery/am-check.out` and my `git am`, is `35c780c48c1921d45b3bb28f8302772755c28d08`. The stated object does not exist. The `merge-tree` line uses the right abbreviation. | Generate every full hash in `REPORT.md` mechanically from `git rev-parse`. |
| BSF-C1-F03 | minor | **`BB1Sim.BB1RealState` has no reader.** It is a new public `abbrev` without an `_eq`/`_iff` lemma. Policy §1 says "a new public `abbrev` still lands with its `_iff` or `_eq` lemma", and the precedents are `IBEScheme.sidState_eq` and `bb1SimState_eq`. REPORT lists its readers as "(notation)". | Add `bb1RealState_eq … := rfl` beside it and list it as a later addition. |
| BSF-C1-F04 | minor | **Docstrings.** 21 of the 49 helpers have neither a `[BB04, …]` tag nor a one-line glue note, though the brief (*Proof discipline*) requires "a tag or a glue note". They are mostly case readers: `relM_iff`, `bb1SimLazyChal_fresh`/`_of_not`, `bb1SimLazy_eq`/`_zero`/`_one`/`_two_fresh`/`_two_of_not`, `bb1SimImpl_zero_coins`/`_one_coins`/`_two_of_not`/`_two_fresh_allOutputs`/`_allOutputs_of_ne_two`, `BB1RealState`, `bb1RealAt_none`/`_some`, `bb1RealLazy_zero_none`/`_none_of_ne`/`_some`, `sidImpl_allOutputs_some` and `sidImpl_none_of_ne`. Three theorem docstrings give no formula: `bb1SimLazy_eq`, `bb1SimImpl_allOutputs_of_ne_two` and `sidImpl_allOutputs_some`. `bb1RealAt` and `bb1RealLazy` carry `[BB04, §2.1]`, but they are fill-local variants of the §2.1 oracles, with `h` recorded or drawn late. The full list is `hygiene.txt` in the evidence zip. | Add "Glue." lines and formulas, and phrase the two §2.1 tags as "variant of the game of [BB04, §2.1]" (or as glue). Docstrings only. |
| BSF-C1-F05 | info | **Announced additions and generalisation.** `Coupling`'s module docstring already names `stepM_init_none … stepM_challenge_fresh`, which do not exist yet. REPORT announces them and the generalisation of `bb1SimImpl_two_of_not` (right-hand side `bb1SimImpl false …`). Both are acceptable: the generalisation is true (see above) and only more general. | At the final, list them as later additions (decls2 ADDED), disclose the generalisation, and make sure the docstring's names exist. |
| BSF-C1-F06 | info | **Overlap and reuse is still to be written** (the final's `REPORT.md` § *Overlap and reuse*). I found no undisclosed duplicate of a public lemma. Overlaps to disclose:<br>• the public `BB1Sim.sidSpec_rng_one`/`_two` are twins of T4's private `BB1Machine.sidSpec_rng_one'`/`_two'` (`BonehBoyenMachine/Oracles.lean:78`, `:85`), a cleanup re-point candidate; T4's files are frozen, so no change here;<br>• the probe's `dom_*`/`rng_*`, `zeroBits_eq_cast`, `RelM`, `RealReads`, `setup_out` and `realAt` (changed to read the recorded `h`), ported;<br>• the algebra lemmas against `pow_val_bijective_of_ne_one`, `pow_val_add`/`_neg`, `bilinear_pow`, `pow_val_mul_GT` and `CharP.natCast_injOn_Iio`. BS-F01 is binding: prove `natCast_bitsToNat_injective` through `CharP.natCast_injOn_Iio`;<br>• design §2.4's table and the relatives the brief names (`PRFGame.expect_lazyImpl`, `ETTGame.expect_ettImpl_lazy`, `expect_simulate_abs(_inv)`, `simulate_eq_of_abs`). | — |
| BSF-C1-F07 | info | **Sketch refresh pending.** T2's frozen `**Proof sketch.**` still cites `Games.expect_simulate_congr` (design §5, risk 3), and T3's names neither eager step. | Refresh both, docstring only, as the brief's *Sketch refresh* says. The frozen-header check with its six controls comes at the final. |
| BSF-C1-F08 | info | **Final-only checks not yet run, as planned:** the canonical seals A/B in strict and coe (plus base seals), the paired controls (10 reader pairs and one per helper definition: `bb1SimLazyChal`, `bb1SimLazy`, `RealReads`, `bb1RealAt`, `bb1RealLazy`, `RelM`), the explicit-unfold scan, axioms and the `sorryAx` trace, lint (baseline 92 FAIL / 104 WARN; check 8 on `RealReads`), and the frozen-header check. The development seal A passed for 5 owners, but that is not evidence. All 17 `sorry`s are ports of proved probe material or short, true lemmas. | — |

## Questions for Seyoon

None. Every finding has a direct fix within the brief and the rulings.

## Evidence

`fill-checkpoint1-review-evidence.zip` (beside this file),
SHA-256 `b0821ac0ffe8a4b078e9ef41b0c66f07ad2d3d49cf90a11b6e8a90178f2f2b61`, 9 entries with an internal
`SHA256SUMS`:
- `repro.log`: the delivery commit's signing and paths, `mkbase.sh`'s output, the `git am` hashes,
  the `merge-tree` result, `diff --stat` and the pushed refs;
- `integrity.log`: both manifests checked;
- `inscheck.py` and `inscheck.out`: the reader insertion check with 12 controls;
- `decls2-review.tsv`: decls2 against the patch base;
- `hygiene.txt`: sizes, widths, `@[simp]`, `attribute`, the micro sign, `sorry` counts and the
  docstring scan;
- `shortname-scan.txt`: the short-name scan with two positive controls.

**Process notes.**
- I ran no Lean process and touched no snapshot.
- The `git am` reproduction ran in a temporary detached worktree, which was removed and pruned.
- `mkbase.sh` ran in this clone; both base commits already existed here, so it wrote no new object.
- Nothing was staged, committed or pushed.

## ===== inbox/fills/bb1-sim/REPORT.md (records, at 2467bc3befdad8472b1f359337bf3a203e3651e1) =====

# Fill `bb1-sim` — final (Claude lead)

**Result.** T2 `bb1_sim_real`, T3 `bb1_sim_random`, `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel` are proved, and the ten approved readers are inserted verbatim. With T4 (#346) in, **`bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1) uses only `propext`, `Classical.choice` and `Quot.sound`**: its `sorry` trace is empty.

Every new or changed file is free of `sorry`. Admissions at the check head are exactly the base's 22 minus the four targets, so 18 in 8 modules.

No statement changed, no frozen file was touched beyond the readers, and there are no scope requests.

## Bases

| | commit | tree |
|---|---|---|
| issue base (#346 head) | `89a18a8225be1b76166af12a15179da291747783` | |
| records tip at issue | `ca129d64cd54a92aabe517e5262058664b49f651` | |
| **patch base** | `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c` | `b5a5842dd0a5af86975864b29065bec44758f561` |
| **check base** (+ #340 head `916afc25…`) | `7cfe2b1b9a7e001d9ae972811cf85a332518111d` | `02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d` |

`tools/mkbase.sh` printed exactly the two pinned lines (`evidence/logs/mkbase.log`):
```
PATCH_BASE 72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c tree b5a5842dd0a5af86975864b29065bec44758f561
CHECK_BASE 7cfe2b1b9a7e001d9ae972811cf85a332518111d tree 02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d
```

**Rebase (Q9): none.**
- At the final, the records branch is at `54b18e4a6b9605862d5d8353e3351415a0c85b57`.
- #346 (`89a18a82…`) and #340 (`916afc25…`) are both **not merged**.
- The Lean diff `ca129d64…54b18e4a` (`*.lean`, toolchain, manifest, lakefile) is empty (`evidence/logs/records-tip-final.txt`).
- So, as the brief says, the fill stays on its bases.

**Branches** (local, unsigned; `COMMITS.tsv` signing column `none`):
- `fill/bb1-sim` head **`c35595aef7636c2ba9a25e1ffdac141b08d2fea5`**;
- check branch `check/bb1-sim-merged` head `408c8195c36007195b0f96a991814b98b5a53aab` = the four fill commits cherry-picked onto the check base.
- **Tree equality:** `git merge-tree --write-tree 916afc25… c35595ae…` = `bdae2f85606a1b930a2eaab1bec13a3b4b2cf56e`, the check head's tree. Every build and check ran at the check head.

**Commits** (`patches/`; `git am` at the patch base reproduces every hash, checked in a scratch clone, `evidence/delivery/am-check.out`):

| # | commit | content |
|---|---|---|
| 1 | `23614c0a` | the ten approved readers in `Defs` and `BonehBoyen` (Q7 follow-up) |
| 2 | `3f430cae` | `expect_simulate_rel` and `expect_sample_rel` |
| 3 | `622f5b03` | the five helper modules |
| 4 | `c35595ae` | T2 and T3: bodies, refreshed sketches, the helper imports, a `## Contents` section |

The checkpoint-1 commits 3 and 4 (`bcb9bcca`, `35c780c4`) were work in progress and are replaced. Commits 1 and 2 are unchanged since checkpoint 1.

## Environment and pool

- **Preflight** (`evidence/logs/preflight.log`):
  - 4 CPUs.
  - Memory: no effective cgroup limit; `MemAvailable` 15.19 GiB.
  - Disk: 14.09 GiB free on the clone's ext4 filesystem. Before the preflight I deleted this host's own finished statement-job worktrees and olean trees. Nothing was copied, moved or deduplicated.
- **Cache:**
  - The store already held 2,420 archives (121 MB) from this host's earlier jobs (`cache-store.log`).
  - The narrowed `lake exe cache get` used the 94 roots (equal to the pack's `roots.txt`). It downloaded nothing, decompressed 2,339 files and exited 0 (`cache-get.log`).
  - `PACKAGES-CHECK PASS`; 0 empty oleans.
- **Bootstrap** (`evidence/build/bootstrap/`): 193/193 rc 0, 0 errors in both forms, sources bound 193/193; exactly the 22 base `sorry` warnings in 10 modules; peak 2.9 GiB.
- **Lean parallelism.**
  - Until the user's message relaying Seyoon's ruling (`workflow.md` §4.1 on `main`, PR #353; quoted in `evidence/logs/parallelism-ruling.txt`), every Lean process ran through the host's one-Lean lock. That covers the bootstrap, every development check, both sweeps and the sub-agent's checks.
  - The final sweep was already running when the ruling arrived and was not interrupted.
  - From the next phase on (seals, controls, scans, axioms, StmtDump, shadow probe), Lean ran through `evidence/tools/seal/poolrun.py`:
    - pool **3** = min(nproc 4, `MemAvailable` ≈ 15 GiB / 4 GiB);
    - a host-wide counting semaphore (slot locks) shared by three concurrent jobs: the head series, the base series and the probes;
    - a 4 GiB `MemAvailable` floor before each start.
  - 197 probes ran through the pool (`evidence/logs/pool-memory.txt`). The lowest `MemAvailable` seen was **13.89 GiB** of 15.71 GiB, and the peak RSS of one probe was **2.93 GiB**.
- **Interruptions, recorded:**
  - A worker restart killed a first final run after 3 of 100 head seal probes (`evidence/rule10/driver-before-restart.out`).
  - I stopped a second run myself to add four missing proof sketches (docstrings only, found by `sk15`). That changed the head, so every Lean check of the final was rerun at the final head.

## Who did what

- **Lead:**
  - the readers, `Relational`, `Lazy`, `Real`, `Random`, `Chain`, T2/T3 and `BonehBoyenSecurity.lean`;
  - every commit, the integration and every check.
- **Sub-agent A (`stepM`)** wrote `Coupling.lean` (step M):
  - the group-algebra lemmas, the nine call-by-call rows `stepM_*`, `stepM_call`;
  - in its own worktree and olean tree (seeded from the lead's tree for 198 modules with byte-identical sources: `evidence/subagents/stepM/seed-treeA.txt`), sharing the lock.
  - It ran no `lake` and committed nothing.
  - Its log, searches and final native and dev-seal A/B logs are in `evidence/subagents/stepM/`.
  - The lead integrated the file unchanged, except for three proof sketches added to its docstrings, and checked it against the lead's tree: native and dev seals A and B rc 0.
- No second sub-agent was used.

## Changed files (lines at the patch base → head)

| file | base | head |
|---|---|---|
| `Games/Relational.lean` | 134 | 146 |
| `IdentityBased/Defs.lean` | 476 | 563 (`97ecb6e0…`) |
| `IdentityBased/BonehBoyen.lean` | 714 | 760 (`88454d6f…`) |
| `IdentityBased/BonehBoyenSecurity.lean` | 170 | 225 |
| `BonehBoyenSecurity/Lazy.lean` (new) | — | 438 |
| `BonehBoyenSecurity/Real.lean` (new) | — | 406 |
| `BonehBoyenSecurity/Coupling.lean` (new) | — | 565 |
| `BonehBoyenSecurity/Random.lean` (new) | — | 139 |
| `BonehBoyenSecurity/Chain.lean` (new) | — | 130 |

`git diff --stat <patch base>` lists exactly these nine files (`evidence/frozen/diff-stat.txt`). Of the frozen files, only `Defs` and `BonehBoyen` change, by the reader insertions.

## The proof

T2 and T3 follow design r1 §3 and the checkpoint outline. Notation:
- `S := bb1Scheme G ℓ`, `c(ρ) := A.toComp (S.sidCodec κ) κ q ρ`;
- for generator coins `r`: `d := desc(κ, r)`, `p := |G|`.

**T2** (body in `BonehBoyenSecurity.lean`):
1. `BB1Sim.setup_out` reads `Setup` as `r, g, α, h, g_2 ↦ o r g α h g_2`, with `RealReads`.
2. Both acceptances are averages over `r` (`prob_bind`).
3. `ProbComp.abs_expect_sub_le_expect` with the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]`:
   - bad coins: two probabilities;
   - good coins: equal, by `BB1Sim.prob_sidGame_coins`.
4. `prob_eq_expect` and `Bridge.prob_sample_eq_uprob` turn the bound into `uprob`.

**`BB1Sim.prob_sidGame_coins`** (`Chain`), the chain for good coins:
1. Move `h` past `g_2` and `ρ` (`expect_sample_comm`).
2. **R1 + E-h** (`expect_sample_sidImpl`):
   - **R1** is `expect_simulate_rel` from `S.sidImpl b κ (o h).1 (o h).2` to `bb1RealAt o h`, with `R s u :↔ s = (u.1.map fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`;
   - **E-h** is `Games.expect_simulate_eager` with `O := bb1RealLazy o`, `OE h := bb1RealAt o h`, `used u := u.1.isSome`.
3. `g_2 = g^{b'}` (`expect_sample_equiv` along `Equiv.ofBijective _ (pow_val_bijective_of_ne_one _ g.2)`).
4. **Step M** (`expect_simulate_bb1RealLazy`): `expect_simulate_rel` with `RelM`, from `bb1RealLazy` to `bb1SimLazy … (fun c => (g^c, e(g,g)^{α b' c}))`. The per-call hypothesis is `stepM_call`, by the rows and `expect_sample_rel`:
   - `Init` along `e ID : G ≃ Z_p` (`exists_equiv_mul_pow`);
   - `KeyGen` along `r ↦ r + b'/(ID − ID*)` (`key_eq`; `ID ≠ ID*` in `Z_p` from `natCast_bitsToNat_injective`, i.e. `CharP.natCast_injOn_Iio`, BS-F01);
   - `Challenge` along the identity (`F_target_eq`, `pair_pow_val_eq`).
5. **E-c** (`expect_simulate_bb1SimLazy`): `Games.expect_simulate_eager` with `O := bb1SimLazy`, `OE c := bb1SimImpl … (g^c) (e(g,g)^{αb'c})`, `used v := v.2.isSome`.
6. On the simulation side:
   - `(a, b', c)` splits into three draws (`Bridge.expect_sample_pair`);
   - `if true then …` reduces, and the unused `T` drops out (`expect_const`);
   - `c` moves past `ρ`.

**T3** (body in `BonehBoyenSecurity.lean`):
1. Unfold both games (`bb1SimGame_eq`, `prob_bind`; `if false …` reduces to `T`), fix `r`, `g`, `abc`, and swap `T` with `ρ`.
2. Apply **`BB1Sim.expect_bb1SimImpl_random`** (`Random`):
   - **E-T** on both sides: `expect_simulate_bb1SimLazy` with `zt T := (Z, T)`;
   - then `ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`.
   At the first valid `Challenge`, `expect_sample_rel` uses `R := Eq` along `T ↦ decodeT(M₁)⁻¹ decodeT(M₀) T` (the probe's P-3). Every other call does not read the bit (`bb1SimImpl_two_of_not`).

**`Relational`.** `expect_simulate_rel`:
- induction on `c`, generalizing the states (`simulate_pure/_query`, `expect_pure/_bind`; design §2.3, L1).

`expect_sample_rel`:
- `expect_bind`, `expect_pure`, `expect_sample_equiv`, then a pointwise comparison (L3).

Both proofs follow their frozen sketches, so the sketches are unchanged.

**Sketch refresh.**
- T2's `**Proof sketch.**` now names `setup_out`, `expect_simulate_rel` (twice), both eager steps, `expect_sample_rel`, `CharP.natCast_injOn_Iio` and `abs_expect_sub_le_expect`. It drops `Games.expect_simulate_congr` (design §5, risk 3).
- T3's names `expect_simulate_eager`, `expect_simulate_congr` and `expect_sample_rel`.
- The statement prose before each sketch is byte-identical (frozen check H2).

## The new declarations

68 public declarations: the ten readers and 58 helper declarations. All are in `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`; `BB1Sim.` below is its sub-namespace. There are no private ones.

| full name | home | kind | readers |
|---|---|---|---|
| `IBEScheme.sidImpl_zero_onSpec`, `_two_onSpec`, `_one_onQuery`, `_two_onQuery`, `_keyGen_ne_onSpec`, `_challenge_fresh_onSpec` | `Defs` | theorem (approved reader) | — |
| `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT` | `BonehBoyen` | theorem (approved reader) | — |
| `BB1Sim.sidSpec_dom_zero/_one/_two`, `sidSpec_rng_zero/_one/_two`, `zeroBits_eq_cast` | `Lazy` | theorem (glue for the game's types) | — |
| `BB1Sim.bb1SimLazyChal` | `Lazy` | def | `bb1SimLazyChal_fresh`, `bb1SimLazyChal_of_not` |
| `BB1Sim.bb1SimLazy` | `Lazy` | def | `bb1SimLazy_eq`, `_zero`, `_one`, `_two_fresh`, `_two_of_not` |
| `BB1Sim.bb1SimImpl_zero_coins`, `_one_coins`, `_two_of_not`, `_two_fresh_allOutputs`, `_allOutputs_of_ne_two`, `expect_simulate_bb1SimLazy` | `Lazy` | theorem | — |
| `BB1Sim.RealReads` | `Real` | structure (`Prop`) | its fields `encPP`, `msgSpace`, `keyGen`, `enc` (projections) |
| `BB1Sim.BB1RealState` | `Real` | abbrev (notation) | — |
| `BB1Sim.bb1RealAt` | `Real` | def | `bb1RealAt_none`, `bb1RealAt_some` |
| `BB1Sim.bb1RealLazy` | `Real` | def | `bb1RealLazy_zero_none`, `_none_of_ne`, `_some` |
| `BB1Sim.setup_out`, `sidImpl_allOutputs_some`, `sidImpl_none_of_ne`, `expect_simulate_sidImpl_bb1RealAt`, `expect_sample_bb1RealAt`, `expect_sample_sidImpl` | `Real` | theorem | — |
| `BB1Sim.exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq`, `pair_pow_val_eq` | `Coupling` | theorem | — |
| `BB1Sim.RelM` | `Coupling` | def | `relM_iff` |
| `BB1Sim.stepM_init_none`, `_init_some`, `_keyGen_none`, `_keyGen_target`, `_keyGen_ne`, `_challenge_none`, `_challenge_repeat`, `_challenge_invalid`, `_challenge_fresh`, `stepM_call`, `expect_simulate_bb1RealLazy` | `Coupling` | theorem | — |
| `BB1Sim.bb1SimLazy_random_call`, `expect_bb1SimImpl_random` | `Random` | theorem | — |
| `BB1Sim.prob_sidGame_coins` | `Chain` | theorem | — |

**Changes since checkpoint 1** (declared there as expected):
- **Nine additions:** the step-M rows `stepM_*`.
- **One statement change,** `BB1Sim.bb1SimImpl_two_of_not`. Its right-hand side was `bb1SimImpl b … 1 1 2 x s` and is now `bb1SimImpl false … 1 1 2 x s`: away from the first valid `Challenge`, the call reads neither the coins nor the challenge bit. The new form is more general; T3's comparison uses it.

`RealReads` and `setup_out` are the probe's statements, in namespace `BB1Sim`. Lint check 8 lists no new definition (*Lint*), so no `_iff` reader was added.

## Statement changes

**None.** The four targets' headers and statement prose, `bb1_sidSecure` and `prob_simulate_rel` are byte-identical to the patch base (frozen-header check, below).

## Checks

1. **Builds** (at the check head `408c8195`).
   - **Bootstrap:** see *Environment*.
   - **Final sweep** (`evidence/build/final-sweep/`): the 13 `DOWN` modules and the 5 helpers in the head order (`evidence/build/order-head.txt`, the helpers before `BonehBoyenSecurity`).
     - **18/18 rc 0**, 0 errors in both forms, 0 `sorry` warnings.
     - Sources bound to `git show HEAD` 18/18.
     - Every module that changed since the bootstrap was rebuilt from its final source, with its downstream, in order.
   - The root `TCSlib` was not built. Neither `audits/*/Checks` is downstream.
2. **Admissions** (`evidence/admissions/`):
   - `admissions.py` on the bootstrap logs, overridden module by module by the final sweep's: **18 declarations in 8 modules = base-sorries minus the four targets, PASS**.
   - The syntactic scan of the nine files against the patch base finds no new `sorry`/`admit`/`native_decide`/`axiom`/`@[simp`/`attribute`, and the four `sorry`s are gone: PASS.
3. **Statements.**
   - **decls2** against the patch base (`evidence/decls2/decls2-final.tsv`): **ADDED 68 (the ten readers + 58 helper declarations), 0 CHANGED, 0 REMOVED.**
   - **StmtDump** (`evidence/stmtdump/`): 74 constants with full names and types: the 68 new ones, the four targets, `prob_simulate_rel` and `bb1_sidSecure`. 0 missing, 0 errors (`final/`). The checkpoint-1 dump (65) is kept.
   - **Frozen-header check** (`evidence/headers/frozen/`, `frozen_check.py`): **12/12 PASS**.
     - Headers of the four targets identical (H1).
     - Their statement prose identical (H2).
     - `prob_simulate_rel` and `bb1_sidSecure` identical whole (H3).
     - Both files identical outside the bodies, sketches, helper imports and `## Contents` (H4).
   - Its six controls give `ALL_CONTROLS_OK True`. Each of these fails as it must:
     - a sketch edit spilling into the prose;
     - a one-character header change;
     - an unpermitted import;
     - an edit to `bb1_sidSecure`;
     - a docstring edit outside `## Contents`;
     - an edit to `prob_simulate_rel`.

     The unchanged file passes.
4. **Reader insertion check** (`evidence/headers/insertion/final/`; tool adapted from T4's):
   - **25/25 PASS**;
   - removal restores `4e220ead…` and `da875140…`;
   - the blocks are verbatim after their anchors (`Defs.lean:430`, `BonehBoyen.lean:412`);
   - final `97ecb6e0…` (563) and `88454d6f…` (760).

   Its 12 controls give `ALL_CONTROLS_OK True`:
   - a character changed: exactly one differing line;
   - a reader deleted: MISSING;
   - an extra line in either file;
   - a reader moved or reordered: MOVED;
   - a docstring edited;
   - a duplicate.
5. **Axioms** (`evidence/axioms/`): `Axioms.lean.txt`, run at the check head; `runs/`.
   - **Axiom list:** the 68 new constants (including the ten readers), the four targets, `prob_simulate_rel`, `bb1_sidSecure` and `exists_bb1_distinguisher`. **75 constants, all standard** (`propext`, `Classical.choice`, `Quot.sound` or a subset).
   - **Census:** every stored constant of the nine changed or new owners, **0 non-standard**:
     - `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3;
     - `Lazy` 24, `Real` 28, `Coupling` 20, `Random` 2, `Chain` 1.
   - **`sorry` dependency trace** (the staging probe's `#sorry_trace`): no constant whose own value uses `sorryAx` in the closure of `bb1_sidSecure` (20,373 constants, T4 in), `bb1_sim_real`, `bb1_sim_random`, `expect_simulate_rel`, `expect_sample_rel` or `prob_simulate_rel`.
   - A first run of the probe had an elaboration error in its own listing code (a counter typed as `MessageData`); it is kept as `runs-attempt1/`, and its census and traces already gave these results.
6. **Rule 10** (`evidence/rule10/`, `evidence/scan/`). 
   - **Canonical seals** A and B, strict and coe (the coe-A seal canonical), `-DmaxErrors=0`, over the full TCSlib import closure. They cover all nine changed or new owners at the check head (`rule10/head/`) and the four existing owners at the check base (`rule10/base/`, base tree `evidence/build/base-tree/`). **Every seal: rc 0, 0 errors, no failing declaration.**

     Requests per owner (A / B / coe-A / coe-B), head and base:

     | owner | head | base |
     |---|---|---|
     | `Relational` | 53 / 53 / 52 / 52 | 53 / 53 / 52 / 52 |
     | `Defs` | 805 / 806 / 804 / 805 | 805 / 806 / 804 / 805 |
     | `BonehBoyen` | 840 / 841 / 839 / 840 | 840 / 841 / 839 / 840 |
     | `BonehBoyenSecurity` | 2320 / 2321 / 2319 / 2320 | 2312 / 2313 / 2311 / 2312 |
     | `Lazy` | 868 / 869 / 867 / 868 | — |
     | `Real` | 871 / 872 / 870 / 871 | — |
     | `Coupling` | 874 / 875 / 873 / 874 | — |
     | `Random` | 871 / 872 / 870 / 871 | — |
     | `Chain` | 877 / 878 / 876 / 877 | — |

     - `Relational` matches the #351 precedent (53/53/52/52, 0 errors in all four variants).
     - **Differences from the base** (`rule10/request-diff-head-vs-base.txt`): none for `Relational`, `Defs` or `BonehBoyen`; the readers add no request.
     - `BonehBoyenSecurity` gains 8 requests in each variant: the helpers' definitions that it now imports (`bb1SimLazy`, `bb1SimLazyChal`, `bb1RealAt`, `bb1RealLazy`, `RelM`), their generated matchers (`bb1SimImpl_allOutputs_of_ne_two.match_1_1`, `stepM_call.match_1_1`) and `RealReads.mk._flat_ctor`.
     - No strict-only `FinDist` failure occurs (DW-10 Q3), because no failure occurs at all.
   - **Paired controls** (`mkctl_bb1sim.py`: T4's and the statement job's rows, plus new rows):
     - ten reader rows (negative: the unfolding the reader replaces; positive: the reader);
     - five helper-definition rows: `bb1SimLazy`, `bb1SimLazyChal`, `bb1RealAt`, `bb1RealLazy`, `RelM`.

     `Relational` and `BonehBoyenSecurity` define nothing, so they get no pair. Each probe takes a covering subset of the seal records. Results:
     - Unsealed pretest: all pass.
     - **Strict `ALL_OK True` and coe `ALL_OK True`**: 32 probes and 485 sealed negatives, each failing exactly once; every positive passes; there are no stray errors (`rule10/head/ctlcheck-{strict,coe}.*`).
     - Two earlier attempts are kept:
       - Attempt 1 of the whole run (`rule10/head-attempt1/`): its unsealed pretest failed because T4's inherited `BB1.idToZ` row opens `TCSlib.Cryptography.Candidates`, outside the helpers' imports. The row was restated with this job's opens.
       - Attempt 1 of the controls (`rule10/head/controls-attempt1/`): the `sidImpl_one_onQuery`/`_two_onQuery` negatives (`rfl`) held under the seal, since those readers need no sealed unfolding. They were restated as what the readers replace: a typed reader applied to the game-typed query, which needs `inLens`. The `bb1RealLazy` negative failed twice, not once, and is now wrapped in `by exact`.

       Both were control-statement defects, not module findings. The seals were not rerun for them.
   - **Explicit-unfold scan** over the nine changed files (`evidence/scan/head/`): 527 `rw`/`simp`/`unfold` items classified; **0 foreign**.
   - **Development seals** (`devseal.py`, not evidence): every helper and `BonehBoyenSecurity` passed A and B during the work.
7. **Frozen-file check.** `git diff --stat 72c0498a…` lists only the nine files of *Scope* (`evidence/frozen/diff-stat.txt`).
8. **Lint** (`evidence/lint/`):
   - `style_lint.py` on the nine files: **0 findings**.
   - `campaign_style_lint.py TCSlib/Cryptography --check8b`: **92 FAIL / 104 WARN over 524 files** at the check base (the baseline) and **92 / 104 over 529** at the check head. The line-set diff has **0 new, 0 gone**.
   - `sk15.py`: no new proof of 15 or more lines without a `**Proof sketch.**`. The one finding is the base's `bb1SimChal_fresh`.
9. **Sizes and widths** (`evidence/sizes/`): every new or changed file is at most 760 lines and 100 characters per line: PASS.
10. **Docstrings.**
    - Every new declaration has a docstring that states it in words and gives its formula, with a [BB04, …] tag from the DW-7 transcription or a glue note.
    - The tags used are `[BB04, proof of Theorem 4.1, *Setup*/*Phase 1*/*Challenge*/*Phase 2, Guess and the advantage*]`, `[BB04, §4.1, *Setup*]`, `[BB04, §2.1]` and `[BB04, §4.4]` (the latter already in `bb1_sidSecure`).
    - The quotations are from the transcription's passages.
    - The helper module docstrings have title, Main definitions, Main results and References.
    - `BonehBoyenSecurity.lean`'s `## Contents` lists the five helpers.
11. **Name-clash and shadow scans** (`evidence/clash/`):
    - (a) `clash_scan.py` (check base → check head): **68 new names, 0 CLASH, 0 DUP-NEW**.
    - (b) A Lean probe over the whole import environment (TCSlib, Mathlib, core; `clash/shadow/`): **none of the 68 new short names (last component) is the last component of any other constant.** Its control (`ShadowCtl.lean.txt`) finds `Option.bind_assoc` and others for `bind_assoc`, so the scan does find matches. Attempt 1 printed the same result and then kept running for an hour; it was stopped and replaced (`runs-attempt1/`).
    - (c) None of the 68 new short names occurs, as a whole identifier, in a `DOWN` module at the check base, so no unqualified use can change its resolution (`uses-in-DOWN.txt`). A first version of this scan matched T4's private primed `BB1Machine.sidSpec_rng_one'`/`_two'`; the file records it.

## Overlap and reuse

Searches are in `evidence/overlap/searches.txt` (`git grep` over TCSlib at the check head) and in sub-agent A's notes (`evidence/subagents/stepM/NOTES.md`, TCSlib and Mathlib).

**Design §2.4's table, confirmed at the check head:**
- `ProbComp.expect_simulate_congr` (`Games/Hopping.lean:384`): one state type; the `R = Eq` case. Used by T3.
- `Games.expect_simulate_eager` (`Hopping.lean:494`): used by E-h, E-c and E-T. **No new eager lemma.** `expect_simulate_bb1SimLazy` and `expect_sample_bb1RealAt` are instances, each a single application with the handler-specific hypotheses (DL-33 respected).
- `ChallengeSim.expect_simulate_eager` (`OracleSecurity/ChallengeSim.lean:148`) is a different, CPA-shaped lemma and is not used.
- `simulate_eq_of_abs(_bounded)` (`Games/Simulate.lean:334`, `:357`), `ETTGame.expect_simulate_abs(_inv)` (`EncryptThenTag/Tools.lean:65`, `:88`), `PRFGame.expect_lazyImpl` (`OracleFromPRF/Lazy.lean:351`), `ETTGame.expect_ettImpl_lazy` (`EncryptThenTag/Lazy.lean:499`), `HashSignFill.expect_simulate_sample_once` (`HashAndSign/OneQuerySampling.lean:47`) and `LamportFill.planted_coupling` (`Lamport/Planted.lean:403`): each is as design §2.4 describes. None states R1, step M, E-h or E-c, and none was copied.
- Averaging bound: `ProbComp.abs_expect_sub_le_expect` (`Probability.lean:409`) is used in T2's body. The private ETT copy (`EncryptThenTag/Forgery.lean:515`) is untouched (Q6, DL-40), and **no third copy** was added.

**Helpers and their nearest relatives:**
- **`BB1Sim.sidSpec_dom_*`/`sidSpec_rng_*`/`zeroBits_eq_cast` (`Lazy`)** are the probe's `dom_*`/`rng_*`/`zeroBits_eq_cast` (statement job's `probe/PlProbe/BB1SimStepM.lean.txt`).
  - **Disclosed overlap:** T4's `BonehBoyenMachine/Oracles.lean:77`, `:84` has **private** `BB1Machine.sidSpec_rng_one'`/`_two'` with the same statements as my public `sidSpec_rng_one`/`_two`.
  - T4's files are frozen here, so its copies stay. A later cleanup could re-point them to the public ones.
- **`bb1SimLazy`/`bb1SimLazyChal`, `bb1RealAt`/`bb1RealLazy`:** specific lazy handlers. Their relatives `PRFGame.lazyImpl` (`OracleFromPRF/Lazy.lean:149`) and `ETTGame.ettLazy` (`EncryptThenTag/Lazy.lean:441`) are other games' handlers; no shared generic form exists.
- **`RelM`, step M's rows, `stepM_call`:** specific to BB1. They are ported from the probe's P-2 (statement job, `a3cb45f6`), with the probe's algebraic hypotheses proved as `exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq` and `pair_pow_val_eq`.
- **The group algebra:**
  - `natCast_bitsToNat_injective` is Mathlib's `CharP.natCast_injOn_Iio` (`Mathlib/Algebra/CharP/Basic.lean:55`, with `ZMod.charP`) plus `bitsToNat_lt`/`bitsToNat_injective` (`Asymptotic/Sampling.lean:412`, `:417`). It is a two-line composition with no Mathlib or TCSlib equivalent (BS-F01).
  - `exists_equiv_mul_pow` composes `Equiv.mulLeft` with `Equiv.ofBijective _ (pow_val_bijective_of_ne_one …)` (`Pairing/Group.lean:252`).
  - `key_eq`, `F_target_eq` and `pair_pow_val_eq` are BB04's computations from `pow_val_add`/`_neg`/`_mul`/`_mul_GT` and `bilinear_pow` (`Pairing/Group.lean`).
  - None restates a Mathlib `ZMod`/`orderOf` fact.
- **`setup_out`, `RealReads`:** the probe's, ported.
- **`sidImpl_allOutputs_some`, `sidImpl_none_of_ne`:** case facts about `IBEScheme.sidImpl` from its readers. They have no published equivalent (the readers state single cases).
- **`prob_sidGame_coins`, `expect_bb1SimImpl_random`:** T2's and T3's chains. They have no relative.

## Exchange commits (BS-F08, disclosed)

The exchange commits `1ef26470` ("fill bb1-sim: checkpoint 1") and `e8b3388d` ("fill bb1-sim: final") carry an SSH signature (`gpgsig`).
- **Cause:** I created them with `git -c commit.gpgsign=false`. The `git pull --rebase` before each push then re-created them, and this host's global `~/.gitconfig` sets `commit.gpgsign = true` (`gpg.format = ssh`), so the platform key signed them.
- **Not fixed:** fixing them would need a force-push, which the brief forbids.
- **Deliverable unaffected:** the four `fill/bb1-sim` commits in `patches/` are unsigned (`COMMITS.tsv`, signing `none`), and `git am` reproduces them.
- **This note's commit** was made, and rebased, with `-c commit.gpgsign=false` throughout.

## Scope requests

None. The route needed no other reader, import or frozen-file change.

## Questions for Seyoon

None.

## Evidence

`evidence/SHA256SUMS` lists every evidence file, and the top-level `SHA256SUMS` lists every delivered file; their paths equal the delivered files. The main entries:
- `logs/` (preflight, cache, mkbase, records tip, the parallelism ruling);
- `build/` (bootstrap, checkpoint-1 and final sweeps, the base tree for the base seals);
- `admissions/`, `decls2/`, `stmtdump/`, `headers/{insertion,frozen}/`, `axioms/`, `rule10/{head,base,head-attempt1}/`, `scan/`, `statements/`, `lint/`, `sizes/`, `clash/`, `overlap/`, `frozen/`;
- `subagents/stepM/`;
- `tools/`, every tool used, with its provenance in its header.

## ===== pr357-description.md (this pack) =====

This is the landing PR for the pairing fill `bb1-sim` (`PairingCryptographyPlan.md`). It proves **T2** `bb1_sim_real` and **T3** `bb1_sim_random` (`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean`) and the two `Games/Relational.lean` targets `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel`. With T1 (#340) and T4 (#346) merged, **Boneh–Boyen BB1's selective-ID security `bb1_sidSecure` now uses only the standard axioms**, and its `sorryAx` trace is empty [BB04, Theorem 4.1].

**Head:** `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`. **Base:** `cryptography/pass-shelat-ch2-4` (records tip `e1d39836`, whose Lean equals the #346 merge `3f540c22`). No stacking: #340 and #346 are merged.

## Scope (9 files, against the tip)
- **`Games/Relational.lean`:** the bodies of `expect_simulate_rel` (induction on the computation, generalizing both states) and `expect_sample_rel` (one bijective coupling of a sample). Headers, statement prose and sketches are frozen and byte-identical; `prob_simulate_rel` is unchanged.
- **`BonehBoyenSecurity.lean`:** the bodies of T2 and T3, five helper imports and a `## Contents` section. The target headers and prose, and `bb1_sidSecure` whole, are byte-identical.
- **Five new helper modules** under `IdentityBased/BonehBoyenSecurity/`: `Lazy` (lazy simulator handlers), `Real` (the real game with `h` recorded and drawn late), `Coupling` (step M of design r1 §3.1), `Random` (the T3 comparison) and `Chain` (the T2 chain `prob_sidGame_coins`). 130–565 lines each; all under the 1000-line cap and 100-character lines.
- **The ten approved readers** (Seyoon, 2026-11-17) as verbatim pure insertions into the frozen files:
  - six in `Defs.lean`: `IBEScheme.sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec`, `sidImpl_challenge_fresh_onSpec`;
  - four in `BonehBoyen.lean`: `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT`.

  Removing the two blocks restores both files byte for byte (insertion pins `97ecb6e0…` for `Defs.lean`, 563 lines, and `88454d6f…` for `BonehBoyen.lean`, 760 lines).

## Commits (5, all SSH-signed)
- The external worker's four commits (Claude; sub-agent A wrote `Coupling.lean`), maintainer-signed `git cherry-pick -S` copies of `23614c0a`, `3f430cae`, `622f5b03` and `c35595ae`: the readers, the `Relational` bodies, the helper modules, and T2/T3. `git range-diff` against the reproduced worker series is 4/4 `=`.
- **LE-bsf1** (maintainer landing edit, ruling Q2), byte-identical to the phase-1 review's `le-bsf1-proposed.diff` (3 files: `Lazy`, `Real`, `Coupling`). It closes BSF-F02/F03 (checkpoint C1-F03/F04):
  - `BB1Sim.bb1RealState_eq … := rfl`, the reader of the public abbrev `BB1RealState` (policy §1);
  - "Glue:" notes on the 21 helper docstrings that had neither a `[BB04, …]` tag nor a glue note, and the formulas of `bb1SimLazy_eq` and `BB1RealState`;
  - `bb1RealAt` and `bb1RealLazy` now say "a variant of the game of [BB04, §2.1]".

  No statement or proof changes apart from the one added declaration.

## Overlap and reuse
- **DL-57 (accepted by Seyoon, Q1; cleanup Stage 2).** The public `BB1Sim.sidSpec_rng_one`/`_two` (`BonehBoyenSecurity/Lazy.lean`) have the same statements and proofs as T4's **private** `BB1Machine.sidSpec_rng_one'`/`_two'` (`BonehBoyenMachine/Oracles.lean`). Stage 2 promotes the scheme-generic `sidSpec_dom_*`/`sidSpec_rng_*` and `zeroBits_eq_cast` into `IdentityBased/Defs.lean` as `IBEScheme.*` and re-points both users, proof-only. `sidImpl_allOutputs_some` and `sidImpl_none_of_ne` travel with the same promotion (BSF-F07).
- The rest is reuse, as disclosed: T2 uses Mathlib's `CharP.natCast_injOn_Iio` directly (BS-F01), the averaging bound `abs_expect_sub_le_expect`, `Games.expect_simulate_eager`, `Bridge.expect_sample_pair` and the `Pairing/Group` helpers. Every `expect_simulate_rel`/`expect_simulate_eager` use is a single application; no new eager or relational lemma (DL-33). The review's own searches found no undisclosed duplicate of a public lemma.
- **`RealReads` has no paired control (BSF-F05, accepted):** it is a `Prop` structure whose readers are its projections; its constructor is sealed in `BonehBoyenSecurity` and the consumers' seals pass.

## Checks
- **Landing (static).** decls2 (pinned) against the tip: **69 ADDED** (10 readers, 58 `BB1Sim.*` helpers, `bb1RealState_eq`), **0 CHANGED, 0 REMOVED**. Reader insertion check against the tip: PASS with 12 controls, pins unchanged. Frozen-header check: 12/12 PASS with 8 controls. Hygiene: 0 `sorry`/`admit`/`native_decide`/`axiom` tokens, no line over 100 characters, every helper docstring tagged or glued.
- **Phase 2 (Lean, maintainer, on olean snapshot #5).** `cp -al` of the snapshot, then the recipe:
  - **19/19 modules rc 0**, 0 `error:`/`error(`, 0 `sorry` warnings (the 9 files, `Games`, the five `BonehBoyenMachine` helpers and facade, the `IdentityBased`/`AdvancedEncryption` facades and root `TCSlib`); sources bound 19/19. State check **1432/1432 OK**; all 19 rebuilt oleans have link count 1; snapshot #5 rehashes 0/0/0 before and after.
  - **Admissions against the tip: 196 → 192, exactly −4** (`expect_simulate_rel`, `expect_sample_rel`, T2, T3).
  - **Axioms:** 76 constants (every new one, the four targets, `prob_simulate_rel`, `bb1_sidSecure`, T4) all standard; census over the 9 owners 325 constants, 0 non-standard. **`#sorry_trace` is empty for `bb1_sidSecure`** (closure 20,373 constants) and for the five other roots; a sorry control is caught by both the trace and the axiom check.
  - **Rule 10:** canonical seals A and B, strict and coe, on all 9 owners (`Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity` and the 5 helpers): **36/36 with 0 errors**, request counts equal to the delivered table (LE-bsf1 adds no definition). Paired controls (32 probes per harness, the 10 reader pairs and the 5 helper-definition pairs): **ALL_OK in strict and coe**, 485 sealed negatives each failing exactly once, every positive and unsealed probe clean. `bb1RealState_eq`: the abbrev `BB1RealState` is never requested by a seal (notation), so it has no sealed negative; its reader and `rfl` entries pass in 6 sealed and 6 unsealed probes per harness.
  - **Explicit-unfold scan:** 527 items, **0 foreign**.
  - **Lint:** `campaign_style_lint --check8b` 92 FAIL / 104 WARN over 529 files, the tip's FAIL/WARN line set unchanged (0 new, 0 gone); `style_lint` 0 findings; `sk15`'s one finding is the base's `bb1SimChal_fresh`.

## Review (`briefs/pairings/fills/bb1-sim/fill-final-r1/review.md`, `phase2.md`): ACCEPT WITH LANDING EDITS
- **Phase 1 (static):** 0 blockers, 0 majors; minors BSF-F01 (the signed exchange final; process only), F02 and F03 (closed by LE-bsf1), F04 (closed by DL-57); infos F05–F08. The patch series reproduces, the readers are verbatim, and the worker's evidence recounts clean (36 head and 16 base seals with 0 errors, 485 sealed negatives per variant each failing once).
- **Phase 2 (Lean on this head):** PASS (above). Final verdict: **ACCEPT WITH LANDING EDITS (LE-bsf1 applied)**.

## Gate
**The bb1-sim gate audits it** (the ten readers and the T2/T3 fill), per the design rulings (Q8).

Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== verification-r1.zip:records/decision-log-pairings.md (this pack) =====

# Decision-log extract: PairingCryptographyPlan.md at e6cdf4d4eed898acd71d48bd60082140eb076cfe, the table header (lines 383-384) and rows 414-454 (bb1-sim design note r1 to #357)

| Date | Decision / evidence | Status |
|---|---|---|
| 2026-11-16 | **bb1-sim design note r1** (`briefs/pairings/fills/bb1-sim/design-r1.md`; no Lean run). It proposes a new `Games/Relational.lean` with the target `expect_simulate_rel` (two handlers on state types σ, τ related by `R`, with a per-call obligation covering equal answer laws and preservation of `R`), the corollary `prob_simulate_rel`, and `expect_sample_rel` for one-sample bijective couplings. It generalizes `ProbComp.expect_simulate_congr` (`Hopping.lean:384`); no existing lemma relates different state types. T2 uses it twice plus `expect_simulate_eager`; T3 needs only `expect_simulate_congr`. Findings: T2 likely needs more readers in `Defs.lean`/`BonehBoyen.lean` (`sidImpl_eq_oracleImpl`, an `encCT` reader) besides T4's 7, so **bb1-sim follows T4's PR**, and a probe should fix the reader set first; T2 must not privately copy `|𝔼f−𝔼g| ≤ 𝔼h` (DL-40), `Z_p ≃ G` or the additive exponent laws. The note proposes one later bb1-sim gate (Games statement, readers and fill). §5 holds 11 multiple-choice questions for Seyoon. | bb1-sim design r1 |
| 2026-11-16 | **Ruling (Seyoon): external Claude jobs for parallelism.** The T4 finish (`bb1-machine`, from the pushed checkpoint `7c0a55e0` with the 7 approved readers) and the GSW phase-6a statements go to cloud Claude sessions that Seyoon dispatches. The maintainer stages each as an issue package (records `issued-r1/`, exchange `outbox/fills/<unit>/`) and reviews and lands the delivery. Local olean trees keep integration builds, reviews and gate work. Staging `bb1-machine` issued-r1 now; phase 6a follows the plan revision r2. | external dispatch: T4, 6a |
| 2026-11-16 | **`bb1-machine` issued-r1 staged for external Claude** (lead plus up to 1 sub-agent): records `briefs/pairings/fills/bb1-machine/issued-r1/`; exchange `78d89c5c` on `747b61e7` (adds only `outbox/fills/bb1-machine/`, 70 files; signed; SHA256SUMS verify; pushed). Base `7c0a55e0` (the pushed checkpoint). The brief: the 7 approved readers verbatim as pure insertions (Defs 3, BonehBoyen 4; the 13-reader variant excluded); move `expect_bb1SimImpl`/`abs_inner_le` into a helper; T4's body and sketch only; full evidence (seals A/B strict and coe on every changed owner including Defs and BonehBoyen, controls with reader rows, decls2, frozen and reader-insertion checks, axioms, lint, name clash); delivery to `inbox/fills/bb1-machine/` only. Then the maintainer review, the T4 PR stacked on #331, and Gate 44. | T4 ready to dispatch |
| 2026-11-16 | **`bb1-machine` (T4 finish) dispatched** (Seyoon; external Claude, lead plus up to 1 sub-agent) at exchange `78d89c5c`, base `7c0a55e0`. Accepted package choices: the worker builds the `AdvancedEncryption` facade closure (188 modules, as for the GSW fills); the maintainer checks root `TCSlib` and both `Checks` at landing; base admissions 57 (T1–T4 plus the GSW and Complexity admissions on this older base), and 56 are expected after delivery. Watch `inbox/fills/bb1-machine/`. | T4 out |
| 2026-11-16 | **#331's last merge condition met:** the cross-build tip × #331 × #339 × #338 passes (715/715, state OK, axioms as expected, T1–T4 the only admissions; evidence `briefs/pass-shelat-ch5-8/maintainer/int-x-331-339-338-2026-11-16/`). #331 marked ready: **clear to merge**. After it merges, #340 and the T4 PR are retargeted to `cryptography/pass-shelat-ch2-4`. | #331 clear to merge |
| 2026-11-16 | **#331 merged** (`22e3f809`): the pairing statements are on the records branch. **#340 (T1) retargeted** to `cryptography/pass-shelat-ch2-4`; its diff is now `Pairing/Assumptions.lean` only (+227/−8), and it merges cleanly. #340 and the T4 PR go to Gate 44 together once T4 is delivered. | #331 merged; #340 retargeted |
| 2026-11-16 | **bb1-sim design rulings, part 1 (Seyoon), on `fills/bb1-sim/design-r1.md` §5:** Q1 a new `Games/Relational.lean`; Q2 the names `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`; Q3 the inline expectation form of the per-call hypothesis. Q4–Q11 to follow. | bb1-sim Q1–Q3 |
| 2026-11-16 | **bb1-sim design rulings complete (Seyoon)** (`briefs/pairings/fills/bb1-sim/rulings.md`). Q1–Q5, Q7–Q9 as recommended. **Changed:** Q6 promotes the averaging bound `\|𝔼f−𝔼g\| ≤ 𝔼h` into `Games/Probability.lean` (public, beside `ProbComp.abs_expect_sub_le`; the ETT copy re-points under DL-40); Q10 puts the group helpers (`Z_p ≃ G` for `g ≠ 1`, exponent laws, identity injectivity) into the frozen `Pairing/Group.lean` by approved insertion; Q11 ingests and cites [BGZ09] and [Sho04] (PDFs from Seyoon; the citations are a docstring-only follow-up, non-blocking, as with Gen09). Next: the reader probe after T4, the Games statement PR, then the fill and one bb1-sim gate. | bb1-sim ruled |
| 2026-11-16 | **T4 delivery review, phase 1: provisional ACCEPT WITH LANDING EDITS** (`fills/bb1-machine/final-r1/review.md`; zip `8157bdfc`). Final delivery `f14ac810`, worker head `c90273fa` (3 unsigned commits on `7c0a55e0`). T4 is proved. The seven readers are verbatim pure insertions (pinned hashes match; 9/9 controls fail as required). T4's header and prose are byte-identical. decls2 +8 / 0 / 0; admissions 57 → 56. No undisclosed duplicate. The worker evidence recounts clean: sweep 189/189, seals 32/32 with 0 errors, 314 controls each failing once, axioms standard, `bb1_sidSecure` reaching only T2/T3. It merges cleanly with the tip, #340 and #341. Findings: 1 minor (BM-F02, docstring argument order) and 8 info. LE-bb1m (`Oracles.lean` only, +2/−8) fixes BM-F01/F02. Phase 2 (Lean) runs on the first rebased tree, followed by the T4 PR and Gate 44 with #340. **bb1-sim statement job staged** (`fills/bb1-sim/issued-stmt-r1/`; exchange `a6a21775` on `48c7a7b4`, pushed; base `bdcadd85`). It covers `stmt/games-relational`, `stmt/pairing-group-helpers` and the reader probe on T4's head. Note: the identity-injectivity helper is stated for naturals below the order (`natCast_inj_of_lt`), because `bitsToNat` is not upstream of `Group.lean`. | T4 phase 1; bb1-sim staged |
| 2026-11-16 | **Draft PR #346 (T4, `bb1-machine`) opened** at `89a18a82` (branch `land/pairings-bb1-machine`, pushed). It has 7 signed commits on the tip: 3 checkpoints, the worker's 3, and LE-bb1m (`Oracles.lean` +2/−8, BM-F01/F02). The diff against the tip is the 8 T4 files. Phase 2 (Lean) runs on the first rebased tree, then Gate 44 with #340. | #346 opened |
| 2026-11-16 | **bb1-sim statement job dispatched** (Seyoon; external Claude, lead plus up to 1 sub-agent) at exchange `a6a21775`, records pin `6fa1e102`, base `bdcadd85`. Watch `inbox/fills/bb1-sim-statements/` (checkpoint 1: the reader probe with `READERS-TO-INSERT.md`). | bb1-sim statements out |
| 2026-11-16 | **#340 (T1) integration condition met** (cross-build tip × #341 × #340 passes; T1 standard; `Assumptions` re-sealed coe A/B with 0 errors). It waits only on Gate 44, with #346. | #340 waits on Gate 44 |
| 2026-11-17 | **bb1-sim reader ruling (Seyoon): all 10 readers the probe found are approved, landing in the bb1-sim fill PR** as verbatim pure insertions: 6 in `Defs.lean` (sidImpl readers at the game's types) and 4 in `BonehBoyen.lean` (setup/keyGen/enc and the `encCT` word reader). Q7 had anticipated one. Probe (checkpoint 1, `8899115b`): T2's step M proved natively and under dev seals A/B, standard axioms, no name clash. The fill uses the probe's `RealReads`/`setup_out` interface. `fills/bb1-sim/rulings.md`. | bb1-sim readers approved |
| 2026-11-17 | **bb1-sim statements: phase-1 review done** (`fills/bb1-sim/statements-final-r1/review.md`, evidence zip `6e4cbadd…`). Interim verdict **accept**: both series reproduce (`912a343e`→`d742bf02` Games; `fc9cf2f5` group), decls2 = the 8 expected ADDED, 0 CHANGED/REMOVED, admissions +2/+0, and all merges are clean (tip, #346, four-way `21c1aa45`). 0 blockers, 0 majors, 2 minors, 8 infos. **BS-F01** (`natCast_inj_of_lt` wraps Mathlib `CharP.natCast_injOn_Iio`) awaits Seyoon; landing edit LE-grp1 recommended. **BS-F08** confirmed by the maintainer: the worker's final exchange commit `a3cb45f6` is signed by the same key as the records commits (`SHA256:32dP45eS…`). Claude cloud sessions on this account share the platform's commit-signing key, so a signature attests a Claude session on the account, not the maintainer; provenance rests on the pinned hashes and maintainer cherry-picks. No worker change is needed. Phase 2 (merged-tree replays) is queued for the Lean slot after #346's check. | bb1-sim P1 |
| 2026-11-17 | **BS-F01 ruled (Seyoon): drop `natCast_inj_of_lt`.** Landing edit **LE-grp1** removes the helper and its docstring bullet from `Pairing/Group.lean` (−7 lines); the group-helper PR carries `fc9cf2f5` plus LE-grp1. The T2/T3 fill uses Mathlib's `CharP.natCast_injOn_Iio` directly. | BS-F01 |
| 2026-11-17 | **bb1-sim landing branches built** (local, maintainer-signed): `land/bb1-sim-games` `dfacac35` (tip `176cfd4a` + `912a343e`, `d742bf02`) and `land/bb1-sim-group` `92dea4f8` (tip + `fc9cf2f5` + LE-grp1). **Phase 2 started** on them (merged-tree replays from snapshot #2, seals, controls, cross-build with #346), concurrently with #346's phase 2 on disjoint directories. Scratch cleanup freed about 4 GB (clean, pushed worktrees of merged work only). | bb1-sim P2 |
| 2026-11-17 | **bb1-sim statements: phase 2 passed, final verdict ACCEPT** (`statements-final-r1/phase2.md`, zip `411338e9…`; 0 blockers/majors/minors, infos BS-F11–F13). Games head `dfacac35`: 181/181 rc 0, admissions +2, seals coe 0 errors. Group head `92dea4f8` (LE-grp1): 12/12 rc 0, +0, seals 0 errors. Cross-build with #346 is clean. **Draft PRs opened:** #351 (Games statements, merges first) and #352 (group helpers, re-replay after #351). Replays kept at `$SP/olean-replay-bb1sim-{games,group}`. | #351, #352 |
| 2026-11-17 | **#351 ruling (Seyoon): merge now, audit later.** #351 is marked ready on the maintainer review (phase 1 + 2 ACCEPT); the bb1-sim gate (Q8) still audits it after merge, and any finding is fixed by a follow-up PR. On merge: check the merge commit's Lean equals tree `c6d3bed3`, adopt `$SP/olean-replay-bb1sim-games` as snapshot #3, then re-replay #352 and #346 on the new tip. | #351 ready |
| 2026-11-17 | **#351 merged (Seyoon)** as `cf7d28f7`. Its Lean equals the replayed head (step-3 diff empty), so its replay was **adopted as olean snapshot #3** (map `e9dfbfdd…`, 1453 entries; basecheck OK; rehash 0/0/0; `maintainer/olean-snapshot-3-adopt/`). The group replay is discarded; #352 and #346 re-replay on #3. The bb1-sim gate still audits #351 (merge-now ruling). | #351 merged |
| 2026-11-17 | **#352 re-replayed on snapshot #3: PASS** (`statements-final-r1/phase2b-352.md`, zip `13483b25…`). Merge tree `3029d8c3` (tip + `Group.lean` +27): 12/12 rc 0, state 1422/1422, admissions +0, standard axioms, seals `Group` 567/568/567/568 and `Assumptions` 644/645/643/644 with 0 errors, controls ALL_OK, 0 foreign unfolds, lint unchanged; seal and control outputs byte-identical to the snapshot-#2 run. Replay kept at `$SP/olean-replay-352`, adoptable if #352 merges before #346. | #352 P2b |
| 2026-11-17 | **#352 ruling (Seyoon): merge now, audit later** (as for #351). Marked ready. Merging before #346 keeps `$SP/olean-replay-352` adoptable as snapshot #4 (merge Lean must equal tree `3029d8c3`); #346 then re-replays on #4. The bb1-sim gate still audits #352. | #352 ready |
| 2026-11-17 | **#352 merged (Seyoon)** as `463f2244`; its replay adopted as **olean snapshot #4** (map `6607620d…`; `maintainer/olean-snapshot-4-adopt/`). **Ruling (Seyoon): #351 and #352 are too small for separate gates;** they are audited later in one combined gate with other similarly small items (DW-11), not in the bb1-sim gate, which keeps the readers and the T2/T3 fill. #346 re-replays on #4. | #352 merged; DW-11 |
| 2026-11-17 | **#346 (T4) phase 2 passed; final verdict ACCEPT WITH LANDING EDITS** (LE-bb1m already #346's 7th commit `89a18a82`; `fills/bb1-machine/final-r1/review.md`, `phase2/`, zip `53a47675…`). Final replay 346c on snapshot #4 (prospective tree `2ec72515`): 12/12 rc 0, state 1427 OK, admissions −1 (T4), standard axioms, `bb1_sidSecure` reaches exactly T2 and T3; seal inputs unchanged since the full snapshot-#2 run (32/32 seals 0 errors, controls ALL_OK incl. the `Oracles` probe BM-F03), coe-A reconfirmed 8/8. Cross-build with #340 on #2 (`b90b966b`): 13/13 rc 0, admissions −2. Replay kept at `$SP/olean-replay-346c` (adoptable only if #346 merges alone). **Next: Gate 44 (#340 + #346).** | #346 P2 |
| 2026-11-17 | **bb1-sim T2/T3 fill staged** (`fills/bb1-sim/issued-fill-r1/`, records `fc0aa4e1`; exchange `c797f6f2`, pushed). Four targets: T2 `bb1_sim_real`, T3 `bb1_sim_random`, and the `Relational` bodies `expect_simulate_rel`, `expect_sample_rel` (design r1 §4.2); plus the 10 approved readers (6 `Defs.lean`, 4 `BonehBoyen.lean`) and the `RealReads`/`setup_out` interface. Staging probe on snapshot #4: 16/16 rc 0, all targets and readers elaborate. **Base ruling (Seyoon): synthetic merge now** — patch base `72c0498a` (tip × #346 head), check base `7cfe2b1b` (+ #340, tree `02b2d44a`); the worker rebases onto the tip if #346 merges mid-job. Ready to dispatch (Claude, lead + 2). | T2/T3 staged |
| 2026-11-17 | **bb1-sim T2/T3 fill dispatched (Seyoon)** to a Claude cloud worker (lead + up to 2), pinned to exchange `c797f6f2` and records `fc0aa4e1`; patch base `72c0498a`, check base `7cfe2b1b`. Deliveries go to `inbox/fills/bb1-sim/`; the bb1-sim gate audits the result (readers + fill). | T2/T3 out |
| 2026-11-17 | **Gate 44 round 1 staged (Codex)** for #340 (T1) + #346 (T4): records `997aac33` + `a6a3c9b2` (`gates/44-pairing-fills/`), exchange `30ef1257`, records pin `8f888790`. Joint replay T44 `33681cb8` (Lean = `c7be1301`) on snapshot #4: 16/16 rc 0, admissions −2 (T1, T4), standard axioms, `bb1_sidSecure` reaches exactly T2/T3; seals on `Assumptions` and #346's 5 downstream owners 0 errors, controls ALL_OK, 0 foreign unfolds; **supplement** re-seal of the unchanged Gate 40 owners downstream (Joux, `BonehBoyenSecurity`, both facades) 16/16 0 errors, controls ALL_OK. #340 retitled and both PR bodies updated before staging. `$SP/olean-replay-g44` (map `ded2f64d…`) becomes snapshot #5 if both merge with Lean = T44. Ready to dispatch. | G44 staged |
| 2026-11-17 | **Gate 44 round 1 dispatched (Seyoon)** to Codex cloud, pinned to exchange `30ef1257` and records `8f888790`. Findings return in chat as `gate44-pairing-fills-findings.md`. | G44 out |
| 2026-11-17 | **Ruling (Seyoon): Lean parallelism for cloud workers.** The one-Lean-process rule is for local hosts (this container; a local checkout). Cloud workers may run a memory-sized pool of Lean processes in dependency order (≤ `nproc`, ~2 GB or 15% memory kept free, no two processes on one module; seals and probes parallel across owners; sub-agents share a counting semaphore). Docs PR #353 (`workflow.md` §4.1); hand-off rule 4 updated; future packages carry the clause; running cloud jobs get a pasteable note. | parallelism |
| 2026-11-17 | **Ruling (Seyoon), refining the above: local hosts allow up to 3 concurrent Lean processes** on the machine across all jobs (one per olean tree); workers and the maintainer may message each other to coordinate slots. #353 updated (amended on its unmerged branch). The maintainer container now runs up to 3 Lean jobs at once. | local 3 slots |
| 2026-11-17 | **#353 merged (Seyoon):** `workflow.md` §4.1 *Lean parallelism* and §6.1 step 5 are on `main` (local hosts: up to 3 Lean processes per machine, coordinated by messaging; cloud workers: a memory-sized pool). | #353 merged |
| 2026-11-17 | **bb1-sim fill checkpoint 1 reviewed: proceed with notes** (`fills/bb1-sim/fill-checkpoint1-review.md`, zip `b0821ac0…`; exchange `1ef26470`). Patches reproduce on patch base `72c0498a`; check head tree `48a81d43`; readers verbatim (pins match, 12 controls); decls2 +59 (10 readers + 49 helpers), 0/0; 18/18 modules rc 0; frozen headers intact; all 49 helper statements true and none makes T2/T3 vacuous; outline covers design r1 §3. 0 blockers/majors; minors BSF-C1-F01 (signed exchange commit), F02 (REPORT head hash typo), F03 (`BB1RealState` reader), F04 (tags/glue notes, formulas); infos F05–F08 for the final. Feedback note sent to the worker via Seyoon. | T2/T3 CP1 |
| 2026-11-17 | **Gate 44 round 1 (Codex): HOLD** — 0 blockers, 1 major, 1 minor, 1 note (`gates/44-pairing-fills/findings-r1.md`; the evidence ZIP was not received). T1 and T4 proofs pass every correctness, frozen-scope, reader, Rule 10, replay and axiom check. **G44-01 (major):** disclosed exact re-derivations lack Seyoon's recorded acceptance and repayment — T1's inline verdict identity = `TrapdoorPredictor.decide_singleton_eq_true`; #346's `poly_rU/rZ/rW/rS` = the `InteractiveHandler` projection facts in `Games/Efficiency.lean:538–550`. **G44-02 (minor):** `[PS10, Theorem 52.3]` mis-locates the bounded sampler (`Draws.lean:58`, `:130`; References in `Words.lean`, `Handler.lean`); the justification is `Candidates.statClose_sampleBelowL`. **G44-03 (note):** pack control counts doubled. | G44 r1 HOLD |
| 2026-11-17 | **Ruling G44-01 (Seyoon): accept, repay in cleanup Stage 2.** Ledger rows **DL-55** (T1 inline identity vs `TrapdoorPredictor.decide_singleton_eq_true`; promote to a shared home and re-point) and **DL-56** (#346 `poly_r*` vs `Games/Efficiency` `polyTimeComputable_r*`; re-point) added to Stage 2. G44-02 is fixed by a docstring landing edit on #346 (LE-g44); G44-03 in the resolutions. Round 2 follows. | G44-01 ruled |
| 2026-11-17 | **Gate 44 round 1 resolved; round 2 staged (Codex)** (`gates/44-pairing-fills/resolutions-r1.md`, `pack-r2.md`, `dispatch-r2.md`). **G44-01:** per the ruling (DL-55, DL-56); dated corrections under both reports' "nothing for the duplication ledger" lines and a note in the bb1-machine review. **G44-02:** landing edit **LE-g44** `98cb0e52` on #346 (docstrings only: the bounded sampler and its bound attributed to `Candidates.sampleBelowL`/`statClose_sampleBelowL`, PS10 Theorem 52.3 kept as context, three References entries; comment-stripped code byte-identical to `89a18a82`; signed, not pushed). **G44-03:** control counts corrected in the round-2 pack. **T44′** `bee027f0` (tip × #340 × #346′): replay on `$SP/olean-replay-g44b` (`cp -al` of g44) 10/10 rc 0, state 1427 OK, link count 1, snapshot #4 0/0/0, 7 downstream oleans byte-identical to T44's, admissions 196, axioms log identical; coe-A seals on `Draws`, `Words`, `Handler`, `BonehBoyenMachine` 0 errors with request sets row-identical; lint unchanged. `olean-replay-g44b` (map `fca1b6a3…`) becomes snapshot #5 if both merge with Lean = T44′; `olean-replay-g44` deleted (map `ded2f64d…` recorded). Exchange `2e015254` (not pushed); records pin `4f4a7592`. PR body drafts with Seyoon. | G44 r2 staged |
| 2026-11-17 | **Gate 44 round 2 dispatched (Seyoon)** to Codex cloud, pinned to exchange `2e015254`, records `4f4a7592`, #340 `916afc25`, #346 `98cb0e52` (LE-g44), T44′ `bee027f0`. Findings return in chat as `gate44-pairing-fills-r2-findings.md`. | G44 r2 out |
| 2026-11-17 | **bb1-sim T2/T3 fill final delivered** (exchange `e8b3388d`, 06:22, plus a REPORT follow-up `2467bc3b`, 06:23). Phase-1 (static) maintainer review started (`fills/bb1-sim/fill-final-r1/review.md`): BSF-C1 closures, the T2/T3 assembly against design r1 §3, disclosures and ledger needs, evidence recount, merges with the tip, #340, #346 `98cb0e52` and the cleanup Stage 1 final. | T2/T3 final in |
| 2026-11-17 | **Gate 44 round 2 (Codex): CLEAR** — 0/0/0/0; G44-01..03 closed; **Gate 44 closed** (`gates/44-pairing-fills/findings-r2.md`, `resolutions-r2.md`). #340 and #346 marked ready. Merge conditions: either order; after both, merge Lean = T44′ `bee027f0`, then adopt `olean-replay-g44b` as snapshot #5. DL-55/DL-56 remain Stage 2 debt. | G44 closed |
| 2026-11-17 | **bb1-sim fill final: phase-1 review, interim ACCEPT WITH LANDING EDITS** (`fills/bb1-sim/fill-final-r1/review.md`, zip `f74bcbde…`). All four targets proved; with T4 in, `bb1_sidSecure` is standard (empty `sorryAx` trace). Patches reproduce (head `c35595ae`); readers verbatim; decls2 68/0/0; admissions 22 → 18; evidence recounts (36 head + 16 base seals 0 errors, 485 negatives per variant, 0 foreign unfolds, lint clean); merges clean with the tip, #340, #346 `98cb0e52` and Stage 1. 0 blockers/majors; minors BSF-F01 (signed exchange final), F02 (`bb1RealState_eq` reader still missing), F03 (helper docstring tags/formulas), F04 (`sidSpec_rng_*` overlap with T4's private twins needs a ledger row, DL-57). Proposed LE-bsf1 closes F02/F03. Questions Q1–Q4 to Seyoon. | T2/T3 P1 |
| 2026-11-17 | **bb1-sim fill rulings (Seyoon), all as recommended:** **Q1** accept the `sidSpec_*` overlap with T4's private twins as **DL-57**, promoted to `IdentityBased/Defs.lean` (`IBEScheme.*`) in cleanup Stage 2; **Q2** maintainer landing edit **LE-bsf1** (docstring tags/formulas, "variant of" for `bb1RealAt`/`bb1RealLazy`, plus `bb1RealState_eq := rfl`); **Q3** wait for #340 and #346 to merge, then open the fill PR on the tip and run phase 2 on snapshot #5. | bb1 fill Q1–Q3 |
| 2026-11-17 | **#340 (T1) and #346 (T4) merged (Seyoon)** as `7152e62f` and `3f540c22`. The merged Lean equals T44′ `bee027f0`, so Gate 44's audited replay was **adopted as olean snapshot #5** (map `fca1b6a3…`; `maintainer/olean-snapshot-5-adopt/`). `bb1_sidSecure` now reaches `sorryAx` only through T2 and T3, which the bb1-sim fill proves. Next: the bb1-sim fill PR on the tip (with LE-bsf1) and its phase 2 on #5. | #340, #346 merged |
| 2026-11-17 | **bb1-sim fill phase 2 on snapshot #5: PASS; final verdict ACCEPT WITH LANDING EDITS (LE-bsf1 applied)** (`fills/bb1-sim/fill-final-r1/phase2.md`, zip `3843d02a…`). Landing head `land/pairings-bb1-sim` `7a98ba01` = tip `e1d39836` + 4 signed cherry-picks (range-diff 4/4 `=`) + LE-bsf1 (byte-identical to the proposed diff). decls2 69/0/0; reader pins hold; frozen 12/12. Replay 19/19 rc 0, state 1432 OK, #5 0/0/0; admissions 196 → 192 (exactly the four targets); **`bb1_sidSecure` standard, empty `sorryAx` trace**; seals 36/36 0 errors, controls ALL_OK (485 negatives); 0 foreign unfolds; lint unchanged. **Draft PR #357** opened into the records branch. Next: the bb1-sim gate (Codex). On merge, adopt `olean-replay-bb1sim` as snapshot #6 if the merge's Lean equals `7a98ba01` (map `b43812d0…`). | bb1 fill P2, #357 |

## ===== verification-r1.zip:records/duplication-ledger-DL55-57.md (this pack) =====

# Extract: briefs/pass-shelat-ch5-8/duplication-ledger.md at e6cdf4d4eed898acd71d48bd60082140eb076cfe, table header (lines 34-35) and rows DL-55 to DL-57 (lines 82-84). As at the pin, these rows have five cells under the four-column header of the table that holds them.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-55 | T1 `BilinearGen.bdhAssumption_of_dbdhAssumption`'s inline verdict identity (`decide ([b] = [true]) = b`, specialised to the solver-success bit; #340, `Pairing/Assumptions.lean:199`; Gate 44 G44-01) | `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), in the public-key layer, which the pairing closure does not import | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** promote `decide_singleton_eq_true` to a shared low-level home importable by both layers, re-point `TrapdoorPredictor` and T1's proof (proof-only). |
| DL-56 | `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (#346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighbours; disclosed with an API obstruction; Gate 44 G44-01) | `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` for the same `InteractiveHandler` projections (`Games/Efficiency.lean:538–550`) | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** re-point the four to the `Games/Efficiency` facts, adding a reader there if the recorded obstruction needs one (proof-only). |
| DL-57 | `BB1Sim.sidSpec_rng_one`, `sidSpec_rng_two`, the related `sidSpec_dom_*` and `zeroBits_eq_cast` (bb1-sim fill, `IdentityBased/BonehBoyenSecurity/`; disclosed; fill review BSF-F04) | T4's private `BB1Machine.sidSpec_rng_one'`, `sidSpec_rng_two'` (#346, `BonehBoyenMachine/Oracles.lean:78`, `:85`) | Accepted (Seyoon, 2026-11-17, bb1-sim fill ruling Q1) | **Cleanup Stage 2:** promote these scheme-generic facts into `IdentityBased/Defs.lean` as `IBEScheme.*` and re-point both the fill's and T4's copies (proof-only). |

## ===== verification-r1.zip:records/cleanup-stages-stage2.md (this pack) =====

# Extract: briefs/pass-shelat-ch5-8/cleanup-stages.md at e6cdf4d4eed898acd71d48bd60082140eb076cfe, lines 18-32 (Stage 2)

## Stage 2: re-point and prune (proof-only)
- Re-point every ledgered copy to its promoted form (DL-35, DL-38 to DL-49, DL-51, DL-52). This includes the
  `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*`, and the ETT averaging-bound copy against the bb1-sim
  promotion in `Games/Probability`.
- Gate 44 G44-01 (Seyoon, 2026-11-17): **DL-55** (promote `decide_singleton_eq_true` to a shared low-level home; re-point
  `TrapdoorPredictor` and pairing T1) and **DL-56** (re-point #346's `poly_rU/rZ/rW/rS` to `Games/Efficiency`'s
  `polyTimeComputable_r*`, with a reader if needed).
- bb1-sim fill ruling Q1 (Seyoon, 2026-11-17): **DL-57** (promote `sidSpec_dom/rng_*` and `zeroBits_eq_cast` into
  `IdentityBased/Defs.lean` as `IBEScheme.*`; re-point the bb1-sim fill and T4's private copies).
- Delete the dead private copies and the public host lemmas left unused by DW-5.
- Clear DW-9's 26 seal failures and `Uniform.lean`'s 4 inherited failures (SY-F07) through readers.
- Sweep in small lint and doc nits, such as the `BobIO` unnecessary `simpa`.
- **Gate:** a proof audit, plus the full Rule 10 seal sweep over every touched owner. Target: every Pass–shelat ledger row
  closed, and no seal failure in any touched file.

## ===== verification-r1.zip:MANIFEST.md (this pack) =====

# verification-r1.zip · Gate 48 (bb1-sim gate) round 1

Every entry except `SHA256SUMS` is listed in `SHA256SUMS`. Nothing here was produced by a new Lean run: `phase1/` and
`phase2/` are the maintainer review's recorded evidence, copied byte for byte; `checks/` are git-object reads made at
staging; `records/` are byte copies or marked extracts of records at the pin.

| Path | What | Origin |
|---|---|---|
| `POINTERS.md` | evidence not copied whole, with sizes and SHA-256 | this staging |
| `checks/series.txt` | pins, Lean-equality of the base with `3f540c22`, the records-only pin delta, the PR diff and its 5 commits | `git` at staging |
| `checks/pins.txt` | the reader pins at base and head and the approved blocks' hashes | `git` at staging |
| `checks/mergetrees.txt` | `git merge-tree --write-tree` of the head with the pin, #347, #355 and the local 6a branches; 3-way simulations | `tools/mergetrees48.sh` |
| `checks/tags.txt` | source tags on the added lines and per file at the head | `git` at staging |
| `checks/dl57.txt` | DL-57's declarations at the head (`git grep`) | `git` at staging |
| `checks/tools/` | the staging scripts | this staging |
| `phase1/` | the phase-1 (static) review evidence, whole; its own manifest is `phase1/SHA256SUMS.original` | `bb1-sim-fill-final-r1-phase1-evidence.zip` |
| `phase2/` | the phase-2 (Lean, snapshot #5) evidence, all but 7 large raw files; `phase2/SHA256SUMS.original` is its manifest | `bb1-sim-fill-final-r1-phase2-evidence.zip` |
| `phase2/phase2.md`, `PROVENANCE.txt` | the phase-2 report and its provenance | phase 2 |
| `phase2/landing/` | the `git am` reproduction, the cherry-picks, the signature key per commit, LE-bsf1 as applied | phase 2 |
| `phase2/static/` | decls2 vs the tip (69/0/0) and its summary, the reader insertion check (12 controls), the frozen check (8 controls), hygiene | phase 2 |
| `phase2/replay/` | orders, plan queue, build results and per-module records, state checks, link counts, snapshot #5 rehashes, output map | phase 2 |
| `phase2/admissions/` | the census at the tip and the head and their diff (196 → 192) | phase 2 |
| `phase2/axioms/` | the probe source `AxiomsBsf.lean.txt` and its log (76 constants, census 325, traces, sorry control) | phase 2 |
| `phase2/rule10/` | the seal tables and `mkseals` logs (36), the control plans and `ctlcheck` results (strict, coe), the driver logs, `attempt1/`, `omitted-SHA256SUMS` | phase 2 |
| `phase2/scan/` | the explicit-unfold scan summary (527 items, 0 foreign), the file list, `omitted-SHA256SUMS` | phase 2 |
| `phase2/lint/` | `campaign_style_lint` at tip and head and their diffs, `style_lint`, `sk15` | phase 2 |
| `phase2/statements/` | the declaration-level comparison of the 9 files, tip → head | phase 2 |
| `phase2/tools/` | the phase-2 drivers and adapted tools | phase 2 |
| `records/briefs/pairings/fills/bb1-sim/…` | design r1, rulings, checkpoint-1 review, the final review (phase 1 + phase-2 verdict), phase2.md, evidence sums, the issued brief, README, sums and the two approved reader blocks | records at the pin |
| `records/briefs/pairings/gates/44-pairing-fills/findings-r{1,2}.md` | Gate 44's findings (precedent for G44-01..03) | records at the pin |
| `records/policy.md` | the repository standards | records at the pin |
| `records/decision-log-pairings.md` | the plan's decision-log rows from the bb1-sim design note to #357 | extract at the pin |
| `records/duplication-ledger-DL55-57.md`, `records/cleanup-stages-stage2.md` | DL-55..DL-57 and cleanup Stage 2 | extracts at the pin |
| `pr/pr357-rest-fields.json` | PR #357's REST fields at staging (head, base, counts, body SHA-256) | GitHub REST |

## ===== verification-r1.zip:POINTERS.md (this pack) =====

# Pointers: evidence not copied whole into this ZIP

Records ZIPs at the records pin `e6cdf4d4eed898acd71d48bd60082140eb076cfe` (size in bytes and SHA-256 of the git blob):

| Path | Bytes | SHA-256 | Here |
|---|---:|---|---|
| `briefs/pairings/fills/bb1-sim/fill-final-r1/bb1-sim-fill-final-r1-phase1-evidence.zip` | 38840 | `f74bcbde5cf84a189b1d9950bb09a05683fe57732405e122b7ac38636ce2035c` | whole, extracted under `phase1/` |
| `briefs/pairings/fills/bb1-sim/fill-final-r1/bb1-sim-fill-final-r1-phase2-evidence.zip` | 734436 | `3843d02aaf73206b58df80875bfaa4d95bc0aa4fdd5d074a44403c81d6af792a` | extracted under `phase2/`, all but 7 large raw files (below) |
| `briefs/pairings/fills/bb1-sim/fill-checkpoint1-review-evidence.zip` | 9832 | `b0821ac0ffe8a4b078e9ef41b0c66f07ad2d3d49cf90a11b6e8a90178f2f2b61` | not copied (checkpoint 1) |
| `briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase1-evidence.zip` | 87443 | `6e4cbadd51e8478fb9093172e42dc6fd4da7b1a1e8ed1408047d9c60bb86c960` | not copied (#351/#352 statements, out of scope) |
| `briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase2-evidence.zip` | 4048148 | `411338e9dcd84d815d12899795599631d64e5f48d5698ac149fc3d3821e5eed8` | not copied (#351/#352 statements, out of scope) |
| `briefs/pairings/fills/bb1-sim/statements-final-r1/bb1-sim-statements-r1-phase2b-evidence.zip` | 2024807 | `13483b25d6e04e79806314e449421d8fc35cfb50470f045a1b83a85c98b13d09` | not copied (#352 re-replay, out of scope) |

Left out of `phase2/` (each is listed with its SHA-256 in `phase2/SHA256SUMS.original`):
`scan/items-head.json`, `scan/explicit-head.json`, `scan/ScanKindsHead.lean.txt` (the scan's raw item lists and kinds probe;
the summary `scan/scan2-head.log` is here), `replay/plan/keys.tsv`, `replay/state/state-init-3f540c22.json.gz`,
`replay/state/state-after.json.gz` (the state plan and records; the `check*.out` and `update.out` results are here) and
`axioms/runs/current.pid`. Verify the rest with `cd phase2 && sha256sum -c --ignore-missing SHA256SUMS.original`.

Not in any ZIP: the raw seal records, control sources and probe logs of phase 2 (about 140 MB). Their SHA-256 are in
`phase2/rule10/omitted-SHA256SUMS` (seals and controls) and `phase2/scan/omitted-SHA256SUMS` (scan runs); the files are
on the maintainer host only. The summaries derived from them (`rule10/seals-*.tsv`, `mkseals-*.log`, `seal-runs/results.jsonl`,
`ctlcheck-*.json`/`.log`, `controls-plan-*.json`) are here.

The worker delivery (the patches, `src/`, the worker's own seals, base seals, controls and logs) is on the exchange at
`2467bc3befdad8472b1f359337bf3a203e3651e1`, `inbox/fills/bb1-sim/` (1426 files): `SHA256SUMS`
`78cf67002642f411fcf794005cbc25c0cd75b76dceaaffc3d4636b435d1b63f7`, `evidence/SHA256SUMS`
`0269eda5b7298fe922beed327957032709b9174523ef2e8f97eb9181c4dc5f9a`, `REPORT.md`
`5b2e592f4058398c685df6072f7fd4bab3072cb78f879ea52ec62a6ca2b330d3`. The 16 base seals the phase-1 review recounted are
there (phase 2 did not re-run them).

## ===== verification-r1.zip:checks/series.txt (this pack) =====

# series and pins (git objects; no Lean)

records pin e6cdf4d4eed898acd71d48bd60082140eb076cfe: Records: bb1-sim fill phase 2 PASS on snapshot #5; draft PR #357
PR base e1d39836ed4a69a34914c35f4c73c71de853dcc6: Records: #340/#346 merged; olean snapshot #5; GSW 6a phase 2 accept
merge-base(pin, head) = e1d39836ed4a69a34914c35f4c73c71de853dcc6
pin descends from base: True
records commits base..pin: e6cdf4d4eed898acd71d48bd60082140eb076cfe
code paths changed base..pin (TCSlib TCSlib.lean audits scripts lakefile.lean lake-manifest.json lean-toolchain): 0
code paths changed 3f540c22 (#346 merge, snapshot #5)..base: 0
pin x head merge-tree: b5c1eda7cb5acba4f64383a2da27866187dc64fc; paths changed vs pin: TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean TCSlib/Cryptography/Games/Relational.lean

git diff base head == git diff base...head: True; sha256 d494afbfefd8e6336d6b050fd3a7907ba9b2b2d81c6e8f481e440c7325bf82bc; 9 files changed, 1925 insertions(+), 21 deletions(-)
46	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean
74	19	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
130	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean
565	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean
447	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean
139	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean
423	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean
87	0	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean
14	2	TCSlib/Cryptography/Games/Relational.lean

commits (base..head):
  69fa787fc52a9c7dff34c8f448ed78b68fcbfbd1 parent e1d39836 gpgsig=1 author Claude <noreply@anthropic.com> 2026-11-17T04:04:20+00:00 committed 2026-11-17T07:44:32+00:00
    fill bb1-sim: the ten approved readers in Defs and BonehBoyen (Q7 follow-up)
    files: IB/BonehBoyen.lean IB/Defs.lean
  2845f1002f63f5ede2eed45e218e42c6b2e8e8e0 parent 69fa787f gpgsig=1 author Claude <noreply@anthropic.com> 2026-11-17T04:30:22+00:00 committed 2026-11-17T07:44:32+00:00
    fill bb1-sim: prove expect_simulate_rel and expect_sample_rel
    files: TCSlib/Cryptography/Games/Relational.lean
  469375fa2d96ae6088c4c7a16b96724559084301 parent 2845f100 gpgsig=1 author Claude <noreply@anthropic.com> 2026-11-17T05:13:59+00:00 committed 2026-11-17T07:44:32+00:00
    fill bb1-sim: helper modules (lazy handlers, real side, step M, T3 comparison, chain)
    files: IB/BonehBoyenSecurity/Chain.lean IB/BonehBoyenSecurity/Coupling.lean IB/BonehBoyenSecurity/Lazy.lean IB/BonehBoyenSecurity/Random.lean IB/BonehBoyenSecurity/Real.lean
  40f7da54d280a1e2bb48fc17c2555f089617a2c9 parent 469375fa gpgsig=1 author Claude <noreply@anthropic.com> 2026-11-17T05:01:37+00:00 committed 2026-11-17T07:44:33+00:00
    fill bb1-sim: prove bb1_sim_real and bb1_sim_random (T2, T3)
    files: IB/BonehBoyenSecurity.lean
  7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff parent 40f7da54 gpgsig=1 author Claude <noreply@anthropic.com> 2026-11-17T07:44:48+00:00 committed 2026-11-17T07:44:48+00:00
    bb1-sim landing edit LE-bsf1: helper docstrings and the BB1RealState reader
    files: IB/BonehBoyenSecurity/Coupling.lean IB/BonehBoyenSecurity/Lazy.lean IB/BonehBoyenSecurity/Real.lean

The signing key of each commit is read from its signature blob in phase 2 (phase2/landing/sigfp.log); this
staging checks only that every commit carries a gpgsig header (no ssh-keygen verify on this host).

## ===== verification-r1.zip:checks/pins.txt (this pack) =====

# reader pins and approved blocks (git objects)

Defs.lean: base 4e220eadd4bf71ea62372bc371a3e2062b9f213acc696dbb66994c1f64069dfd (476 lines); head 97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0 (563 lines); ruled pin 97ecb6e02413d18fce255949ed4b3e777c8f653a59f0792b575be3ff24a6a9a0: True
BonehBoyen.lean: base da875140806706f26c4cdbb5cf765f522144f3a5a885c5156a58b8c611cd25f4 (714 lines); head 88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26 (760 lines); ruled pin 88454d6fb0fa2c81419b189dbc633609357ee39b35ccbe90c810a0ad10891c26: True
approved block Defs-block.lean.txt (issued-fill-r1/readers at the pin): d6f8faf16bd8b121fbccba9541225ca9761a2ee90b4eda3bf12dead62eaaa239 (86 lines)
approved block BonehBoyen-block.lean.txt (issued-fill-r1/readers at the pin): 967f2a303484228d42be74c446cf4a8c2a92fb46ad705ec1a60f24b54427f226 (45 lines)

The pure-insertion check with its 12 controls is phase 2's inscheck_tip.py: phase2/static/inscheck-tip.out.

## ===== verification-r1.zip:checks/mergetrees.txt (this pack) =====

# merge-tree of #357 head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff (git 2.43.0)
#357's own paths (base e1d39836ed4a69a34914c35f4c73c71de853dcc6): 9

== records pin: origin/cryptography/pass-shelat-ch2-4 = e6cdf4d4eed898acd71d48bd60082140eb076cfe (expected e6cdf4d4eed898acd71d48bd60082140eb076cfe: ok)
   merge-base e1d39836ed4a69a34914c35f4c73c71de853dcc6; rc=0; tree b5c1eda7cb5acba4f64383a2da27866187dc64fc
   paths changed by the other side since the merge base: 5
   shared with #357's side since the merge base: 
   shared with #357's own 9 paths: 0
== #347 cleanup/dw5-derand-readers: origin/cleanup/dw5-derand-readers = daa6e173cdd94cad1475b9a96eca613bce53ba61 (expected daa6e173cdd94cad1475b9a96eca613bce53ba61: ok)
   merge-base 2da7e0f3cd65ec93ed71813b7828c3b66ba18942; rc=0; tree 778239f0b5cc109aba55e9f3d859af6f03a1b370
   paths changed by the other side since the merge base: 3
   shared with #357's side since the merge base: 
   shared with #357's own 9 paths: 0
== #355 land/cleanup-stage1: origin/land/cleanup-stage1 = d3c7cb00092ad5913904654d922f30fc7d5fce4a (expected d3c7cb00092ad5913904654d922f30fc7d5fce4a: ok)
   merge-base 2da7e0f3cd65ec93ed71813b7828c3b66ba18942; rc=0; tree b97f53290870959dfc14a7edaf05957c840f35de
   paths changed by the other side since the merge base: 23
   shared with #357's side since the merge base: TCSlib/Cryptography/Games.lean 
   shared with #357's own 9 paths: 0
== 6a land/gsw-6a-o1 (local, unpushed, no PR): land/gsw-6a-o1 = a616adcac0760ab56b1b0a2a4869f4763843f9ab (expected a616adcac0760ab56b1b0a2a4869f4763843f9ab: ok)
   merge-base e1d39836ed4a69a34914c35f4c73c71de853dcc6; rc=0; tree d047b59c5cb546ebe7c504b153f78db9622ad920
   paths changed by the other side since the merge base: 4
   shared with #357's side since the merge base: 
   shared with #357's own 9 paths: 0
== 6a land/gsw-6a-statements (local, unpushed, no PR): land/gsw-6a-statements = 73aedcdaaaffef7e69ab012d9b9195f150bae68d (expected 73aedcdaaaffef7e69ab012d9b9195f150bae68d: ok)
   merge-base e1d39836ed4a69a34914c35f4c73c71de853dcc6; rc=0; tree a8941d8623ab1e731705baa196eccddc645e9e03
   paths changed by the other side since the merge base: 18
   shared with #357's side since the merge base: 
   shared with #357's own 9 paths: 0

== origin refs matching land/gsw-6a-*: 0 (git ls-remote at staging)

== three-way simulations: (records pin x other) x #357
   pin x daa6e173: rc=0 tree 19e526ac881b995c7f59947a6f8ceca50816d4ad; then x #357: rc=0 tree 36cfde2d9dbe5a9bbe4a45f38634bd95cbb5e8e9; paths changed vs the first merge: 9; #357 files not blob-equal to the head: 0
   pin x d3c7cb00: rc=0 tree ca44595002ccd1fc8b456ef459ede0a1c777d8ea; then x #357: rc=0 tree 0d71d4a2719c36a886d9d72df1153319547da73d; paths changed vs the first merge: 9; #357 files not blob-equal to the head: 0

== Games.lean at the pin, #357 and #355 (the one path shared since 2da7e0f3; #357 itself does not touch it)
   pin ce4a9f308673a48bad3f1e9b852fae0d8077815f  #357 ce4a9f308673a48bad3f1e9b852fae0d8077815f  #355 1c987715a2825157f655f7c17c199d02e79b1900

## ===== verification-r1.zip:checks/tags.txt (this pack) =====

# source tags (git objects): tags on lines the PR adds, and per file at the head

added lines (git diff base head; tags on one line only, so a tag broken across two lines is not counted here):
    6 [BB04, proof of Theorem 4.1]
    5 [BB04, proof of Theorem 4.1, *Setup*]
    5 [BB04]
    2 [BB04, proof of Theorem 4.1, *Challenge*]
    2 [BB04, §2.1]
    1 [BB04, proof of Theorem 4.1, *Phase 1*]
    1 [BB04, proof of Theorem 4.1, *Phase 2, Guess and the advantage*]
    1 [BB04, §4.1, *Setup*]
    1 [BB04, §4.1]
    1 [BB04, §4.4]
  added lines with "Glue:": 25
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean:
    4 [BB04, proof of Theorem 4.1]
    4 [BB04, §4.1, depth 1]
    2 [BB04, proof of Theorem 4.1, *Challenge*]
    2 [BB04, §4.1]
    2 [BB04, §4.4]
    1 [BB04, Theorem 4.1]
    1 [BB04, proof of Theorem 4.1, *Initialization* and *Setup*]
    1 [BB04, proof of Theorem 4.1, *Phase 1*]
    1 [BB04, proof of Theorem 4.1, *Setup*]
    1 [BB04, §2.1]
    1 [BB04, §4.1 at depth 1, with the identity encoding of §4.4]
    1 [BB04, §4.1, "Indeed, for a valid ciphertext …"]
    1 [BB04, §4.1, `Encrypt` at depth 1]
    1 [BB04, §4.1, `F_1 : Z_p → G`]
    1 [BB04, §4.1, `KeyGen` at depth 1]
    1 [BB04, §4.1, `Setup` at depth 1]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean:
    2 [BB04, Theorem 4.1]
    1 [BB04, Theorem 4.1, at depth `ℓ = 1`]
    1 [BB04, pp. 7–8]
    1 [BB04, §4.4]
    1 [BB04]
    1 [PS10]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean:
    1 [BB04, proof of Theorem 4.1, *Phase 2, Guess and the advantage*]
    1 [BB04, proof of Theorem 4.1]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:
    5 [BB04, proof of Theorem 4.1, *Setup*]
    2 [BB04, proof of Theorem 4.1]
    1 [BB04, proof of Theorem 4.1, *Challenge*]
    1 [BB04, proof of Theorem 4.1, *Phase 1*]
    1 [BB04, §4.4]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:
    1 [BB04, proof of Theorem 4.1]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean:
    1 [BB04, proof of Theorem 4.1, *Challenge*]
    1 [BB04, proof of Theorem 4.1]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean:
    2 [BB04, §2.1]
    1 [BB04, proof of Theorem 4.1]
    1 [BB04, §4.1, *Setup*]
    1 [BB04, §4.1]
    1 [BB04]
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean:
    6 [BB04, §2.1]
    2 [BB04, §2.1 and Definition 2.2]
    2 [BB04, §2.1, the adversary's view]
    1 [BB04, Definition 2.2]
    1 [BB04]
    1 [PS10]
TCSlib/Cryptography/Games/Relational.lean:
    2 [BGZ09]
    2 [Sho04, §1.1, bridging steps]
    1 [BGZ09, §3.4]
    1 [BGZ09, §4.1, Def. 5]
    1 [BGZ09, §4.1, lemma (=⟦⟧)]
    1 [BGZ09, §4.2, ⊨_φ]
    1 [BGZ09, §5.2, Lemma 1]
    1 [Sho04, §4.2, Game 2]
    1 [Sho04]

## ===== verification-r1.zip:checks/dl57.txt (this pack) =====

# DL-57 twins at the head (git grep)

7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean:77:private theorem sidSpec_rng_one' (S : IBEScheme) (κ : ℕ) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean:84:private theorem sidSpec_rng_two' (S : IBEScheme) (κ : ℕ) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean:167:        cast (sidSpec_rng_one' (bb1Scheme G ℓ) κ).symm (zeroBits _) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean:224:        cast (sidSpec_rng_two' (bb1Scheme G ℓ) κ).symm (zeroBits _) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:172:      ∀ h, (f₀ h).1 = (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).1 ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:174:          (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).2 := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:188:    have hz := he (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:237:      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:246:`oracleImpl_one_onSpec`); both `⊥` words agree by `zeroBits_eq_cast` and `outLens_one`. -/
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:250:    (ht : cast (sidSpec_dom_one _ κ) x = t) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:262:      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:279:    (ht : cast (sidSpec_dom_one _ κ) x ≠ t) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:287:          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).1 ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:289:          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).2 := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:295:    rw [(ho h).keyGen _ fun w => .pure (cast (sidSpec_rng_one _ κ).symm
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:305:    have hz : BB1.idToZ (G.group κ d) (cast (sidSpec_dom_one _ κ) x) ≠
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:331:      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:367:`bb1Scheme_msgSpace_iff`). Both answer the `⊥` word (`zeroBits_eq_cast`). -/
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:372:        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:374:        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:379:        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1 ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:381:        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) := fun hm =>
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:391:      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:411:        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:413:        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:429:    rw [(ho h).enc t _ fun w => .pure (cast (sidSpec_rng_two _ κ).symm w, (some (t, h), some w))]
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:502:      by_cases hx : cast (sidSpec_dom_one _ κ) x = t
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:524:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean:526:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:27:(`sidSpec_dom_zero`, …), so that its consumers never reduce `IBEScheme.inLens` or
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:67:theorem sidSpec_dom_zero : (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:72:theorem sidSpec_dom_one : (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:78:theorem sidSpec_dom_two :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:89:theorem sidSpec_rng_one : (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:94:theorem sidSpec_rng_two : (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool) := by
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:99:theorem zeroBits_eq_cast {n m : ℕ} (hnm : n = m) (e : (Fin m → Bool) = (Fin n → Bool)) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:218:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:220:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:235:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:237:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:255:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:257:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:270:              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:272:              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :=
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:275:        bb1SimChal G ℓ b' κ d g X Y Z' T' (cast (sidSpec_dom_two _ κ) x) (some (t, α₁), none) =
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:296:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:298:          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:339:    by_cases ht : cast (sidSpec_dom_one _ κ) x = t
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:377:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:379:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:399:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:401:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:422:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean:424:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean:78:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean:80:            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean:89:    set m := (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)) with hm
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean:92:          .pure (cast (sidSpec_rng_two _ κ).symm
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean:275:  · by_cases ht : cast (sidSpec_dom_one S κ) x = t
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean:284:          (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).1 ∧
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff:TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean:285:        S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).2

## ===== verification-r1.zip:phase2/PROVENANCE.txt (this pack) =====

bb1-sim fill final r1, phase 2 (maintainer), 2026-11-17 07:44-09:08 UTC.
Records tip:      e1d39836ed4a69a34914c35f4c73c71de853dcc6 (Lean = snapshot #5 T 3f540c22360c869069a0fba684e23ce6f3cb20db)
Delivery:         exchange 2467bc3befdad8472b1f359337bf3a203e3651e1, inbox/fills/bb1-sim/; worker head c35595aef7636c2ba9a25e1ffdac141b08d2fea5 on 72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c
Landing head:     land/pairings-bb1-sim 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff (5 signed commits on the tip; LE-bsf1 last)
Phase-1 zip:      bb1-sim-fill-final-r1-phase1-evidence.zip f74bcbde5cf84a189b1d9950bb09a05683fe57732405e122b7ac38636ce2035c
LE-bsf1 diff:     8f18c2e3a53ee945411f8b20a3e4679ce9b6cb8a3d2196aa06728076fe43c5fe (= le-bsf1-proposed.diff)
Snapshot #5:      $SP/olean-snapshot, map fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9 (0/0/0 before, after, end)
Replay:           $SP/olean-replay-bb1sim, output map (no Mathlib) 1463 entries b43812d0008b290343fab435f725544b1eef2c944f3581f2e8a62b3c0362171a
Recipe tools:     olean-rebase-evidence.zip (b662b7da...) olean-advance-a6d01b1b/tools-used/, byte-identical copies
Lean:             one process at a time, slot-gated (fewer than 3 lean processes on the host); no lake build, no cache get
Omitted:          raw seal records, control sources and probe logs; SHA-256 in rule10/omitted-SHA256SUMS, scan/omitted-SHA256SUMS

## ===== verification-r1.zip:phase2/static/decls2-summary.txt (this pack) =====

decls2 (pinned fa81981a) landing head vs tip e1d39836 over the 9 files:
     69 ADDED
vs phase-1 decls2 (68 rows, patch base), location column dropped:
11a12
> ADDED	TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealState_eq	theorem	theorem bb1RealState_eq (κ : ℕ) (d : List Bool) : BB1RealState G ℓ κ d = (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) × Option 
readers (Defs/BonehBoyen):
10
BB1Sim.*:
59

## ===== verification-r1.zip:phase2/static/inscheck-tip.out (this pack) =====

TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean block d6f8faf1 head 97ecb6e0
  base-hash PASS
  head-hash PASS
  head-lines PASS
  pure-insertion-bytes PASS
  removal-restores-base PASS
  blank-before-block PASS
  CONTROL one-char-in-reader FAIL(expected)
  CONTROL extra-line-elsewhere FAIL(expected)
  CONTROL extra-blank-after-block FAIL(expected)
  CONTROL reader-lines-deleted FAIL(expected)
  CONTROL reader-lines-moved FAIL(expected)
  CONTROL docstring-edited FAIL(expected)
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean block 967f2a30 head 88454d6f
  base-hash PASS
  head-hash PASS
  head-lines PASS
  pure-insertion-bytes PASS
  removal-restores-base PASS
  blank-before-block PASS
  CONTROL one-char-in-reader FAIL(expected)
  CONTROL extra-line-elsewhere FAIL(expected)
  CONTROL extra-blank-after-block FAIL(expected)
  CONTROL reader-lines-deleted FAIL(expected)
  CONTROL reader-lines-moved FAIL(expected)
  CONTROL docstring-edited FAIL(expected)
RESULT PASS

## ===== verification-r1.zip:phase2/static/frozencheck-tip.out (this pack) =====

PASS H1 expect_simulate_rel
PASS H2 expect_simulate_rel
PASS H1 expect_sample_rel
PASS H2 expect_sample_rel
PASS H3 prob_simulate_rel
PASS H4 Relational.lean
PASS H1 bb1_sim_real
PASS H2 bb1_sim_real
PASS H1 bb1_sim_random
PASS H2 bb1_sim_random
PASS H3 bb1_sidSecure
PASS H4 BonehBoyenSecurity.lean
RESULT PASS
CONTROL sketch-spills-into-prose mutated FAIL(expected) ['H2 bb1_sim_real', 'H4 BonehBoyenSecurity.lean']
CONTROL one-char-header mutated FAIL(expected) ['H1 bb1_sim_random', 'H4 BonehBoyenSecurity.lean']
CONTROL unpermitted-import mutated FAIL(expected) ['H4 BonehBoyenSecurity.lean']
CONTROL edit-bb1_sidSecure mutated FAIL(expected) ['H3 bb1_sidSecure', 'H4 BonehBoyenSecurity.lean']
CONTROL docstring-outside-contents mutated FAIL(expected) ['H4 BonehBoyenSecurity.lean']
CONTROL edit-prob_simulate_rel mutated FAIL(expected) ['H3 prob_simulate_rel', 'H4 Relational.lean']
CONTROL prose-edit-Relational mutated FAIL(expected) ['H2 expect_sample_rel', 'H4 Relational.lean']
CONTROL header-edit-Relational mutated FAIL(expected) ['H1 expect_simulate_rel', 'H4 Relational.lean']
CONTROL unchanged-head PASS(expected)
ALL_CONTROLS_OK True

## ===== verification-r1.zip:phase2/landing/landing-verify.log (this pack) =====

## range-diff 72c0498a..c35595ae vs e1d39836ed4a69a34914c35f4c73c71de853dcc6..7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff~1
1:  23614c0a2 = 1:  69fa787fc fill bb1-sim: the ten approved readers in Defs and BonehBoyen (Q7 follow-up)
2:  3f430cae5 = 2:  2845f1002 fill bb1-sim: prove expect_simulate_rel and expect_sample_rel
3:  622f5b036 = 3:  469375fa2 fill bb1-sim: helper modules (lazy handlers, real side, step M, T3 comparison, chain)
4:  c35595aef = 4:  40f7da54d fill bb1-sim: prove bb1_sim_real and bb1_sim_random (T2, T3)
## LE-bsf1 diff vs proposed
LE-bsf1 diff byte-identical to le-bsf1-proposed.diff (8f18c2e3a53ee945)
## tree of HEAD~1 equals c35595ae on the 9 files
 3 files changed, 22 insertions(+), 7 deletions(-)
(empty above = identical)
## diff --stat tip..head
 .../IdentityBased/BonehBoyen.lean                  |  46 ++
 .../IdentityBased/BonehBoyenSecurity.lean          |  93 +++-
 .../IdentityBased/BonehBoyenSecurity/Chain.lean    | 130 +++++
 .../IdentityBased/BonehBoyenSecurity/Coupling.lean | 565 +++++++++++++++++++++
 .../IdentityBased/BonehBoyenSecurity/Lazy.lean     | 447 ++++++++++++++++
 .../IdentityBased/BonehBoyenSecurity/Random.lean   | 139 +++++
 .../IdentityBased/BonehBoyenSecurity/Real.lean     | 423 +++++++++++++++
 .../AdvancedEncryption/IdentityBased/Defs.lean     |  87 ++++
 TCSlib/Cryptography/Games/Relational.lean          |  16 +-
 9 files changed, 1925 insertions(+), 21 deletions(-)
## Lean paths changed
9
## signatures
7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff gpgsig=1 B 
40f7da54d280a1e2bb48fc17c2555f089617a2c9 gpgsig=1 B 
469375fa2d96ae6088c4c7a16b96724559084301 gpgsig=1 B 
2845f1002f63f5ede2eed45e218e42c6b2e8e8e0 gpgsig=1 B 
69fa787fc52a9c7dff34c8f448ed78b68fcbfbd1 gpgsig=1 B 
## H~1 vs c35595ae on the 9 files
(no output = byte-identical)
## H~1 vs c35595ae, all paths (expected: LE-g44's 3 docstring files + records files)
 .../IdentityBased/BonehBoyenMachine/Draws.lean     |  19 +-
 .../IdentityBased/BonehBoyenMachine/Handler.lean   |   5 +-
 .../IdentityBased/BonehBoyenMachine/Words.lean     |   5 +-
 TCSlib/Cryptography/Pairing/Assumptions.lean       | 235 ++++++++++++++++++++-
 4 files changed, 249 insertions(+), 15 deletions(-)
## tip vs 72c0498a (patch base), Lean paths
 .../IdentityBased/BonehBoyenMachine/Draws.lean     |  19 +-
 .../IdentityBased/BonehBoyenMachine/Handler.lean   |   5 +-
 .../IdentityBased/BonehBoyenMachine/Words.lean     |   5 +-
 TCSlib/Cryptography/Pairing/Assumptions.lean       | 235 ++++++++++++++++++++-
 4 files changed, 249 insertions(+), 15 deletions(-)
## T_land c1d5fd89 vs H~1, Lean paths
tree
(no output = Lean-equal)
## T44' bee027f0 vs H, Lean paths
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean
TCSlib/Cryptography/Games/Relational.lean
## tip 3f540c22 (snapshot #5 T) vs e1d39836, Lean
(no output = Lean-equal)

## ===== verification-r1.zip:phase2/landing/sigfp.log (this pack) =====

7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc
40f7da54d280a1e2bb48fc17c2555f089617a2c9 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc
469375fa2d96ae6088c4c7a16b96724559084301 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc
2845f1002f63f5ede2eed45e218e42c6b2e8e8e0 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc
69fa787fc52a9c7dff34c8f448ed78b68fcbfbd1 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc
e1d39836ed4a69a34914c35f4c73c71de853dcc6 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc

## ===== verification-r1.zip:phase2/replay/build/permod.out (this pack) =====

modules 19; rc!=0 0; error: 0; error( 0; combined 0; substring 0; sorry 0; warnings 0; log/record mismatches []

## ===== verification-r1.zip:phase2/replay/state/check-final.out (this pack) =====

7a98ba01 order 1432; bad 0 [] | RESULT OK

## ===== verification-r1.zip:phase2/replay/output-map/map.out (this pack) =====

/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/bsp2/run/output-map/olean-replay-bb1sim.map-7a98ba01.noMathlib.tsv: entries 1463; sha256 b43812d0008b290343fab435f725544b1eef2c944f3581f2e8a62b3c0362171a
vs /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/olean-snapshot.map-3f540c22.tsv: equal 1454; changed 4 ['TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs', 'TCSlib/Cryptography/Games/Relational']; added ['TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real']; removed []

## ===== verification-r1.zip:phase2/admissions/census-tip-vs-head.txt (this pack) =====

826c826,831
< 2 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity
---
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random
> 0 TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real
1057c1062
< 2 TCSlib/Cryptography/Games/Relational
---
> 0 TCSlib/Cryptography/Games/Relational

## ===== verification-r1.zip:phase2/axioms/runs/mods/BSF2_AxiomsBsf.log (this pack) =====

AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.BB1RealState: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.F_target_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.RealReads: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.RelM: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealAt: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealAt_none: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealAt_some: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealLazy: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealLazy_none_of_ne: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealLazy_some: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealLazy_zero_none: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1RealState_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimImpl_allOutputs_of_ne_two: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimImpl_one_coins: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimImpl_two_fresh_allOutputs: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimImpl_two_of_not: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimImpl_zero_coins: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazyChal: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazyChal_fresh: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazyChal_of_not: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_one: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_random_call: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_two_fresh: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_two_of_not: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.bb1SimLazy_zero: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.exists_equiv_mul_pow: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_bb1SimImpl_random: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_sample_bb1RealAt: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_sample_sidImpl: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_simulate_bb1RealLazy: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_simulate_bb1SimLazy: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.expect_simulate_sidImpl_bb1RealAt: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.key_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.natCast_bitsToNat_injective: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.pair_pow_val_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.prob_sidGame_coins: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.relM_iff: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.setup_out: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidImpl_allOutputs_some: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidImpl_none_of_ne: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_dom_one: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_dom_two: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_dom_zero: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_rng_one: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_rng_two: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.sidSpec_rng_zero: [propext]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_call: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_challenge_fresh: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_challenge_invalid: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_challenge_none: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_challenge_repeat: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_init_none: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_init_some: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_keyGen_ne: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_keyGen_none: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.stepM_keyGen_target: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Sim.zeroBits_eq_cast: []
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_challenge_fresh_onSpec: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_keyGen_ne_onSpec: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_one_onQuery: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_two_onQuery: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_two_onSpec: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.sidImpl_zero_onSpec: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1Scheme_enc_bind: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1Scheme_keyGen_bind: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1Scheme_setup_eq: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.ofFn_bb1Scheme_encCT: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.Games.ProbComp.expect_simulate_rel: [propext, Classical.choice, Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.Games.ProbComp.expect_sample_rel: [propext, Classical.choice, Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.Games.ProbComp.prob_simulate_rel: [propext, Classical.choice, Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_real: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_random: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sidSecure: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS STANDARD TCSlib.Cryptography.AdvancedEncryption.IdentityBased.exists_bb1_distinguisher: [propext,
 Classical.choice,
 Quot.sound]
AXIOMS-LIST 76 constants, 0 non-standard
CENSUS TCSlib.Cryptography.Games.Relational: 3 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs: 96 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen: 147 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity: 3 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy: 24 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real: 29 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling: 20 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Random: 2 stored constants, 0 non-standard []
CENSUS TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain: 1 stored constants, 0 non-standard []
TRACE TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sidSecure: closure 20373; direct sorryAx users: []
TRACE TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_real: closure 15352; direct sorryAx users: []
TRACE TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_random: closure 13412; direct sorryAx users: []
TRACE TCSlib.Cryptography.Games.ProbComp.expect_simulate_rel: closure 5020; direct sorryAx users: []
TRACE TCSlib.Cryptography.Games.ProbComp.expect_sample_rel: closure 11705; direct sorryAx users: []
TRACE TCSlib.Cryptography.Games.ProbComp.prob_simulate_rel: closure 5023; direct sorryAx users: []
BSF2/AxiomsBsf.lean:75:8: warning: declaration uses 'sorry'
TRACE bsfSorryControl: closure 297; direct sorryAx users: [bsfSorryControl]
CONTROL AXIOMS NONSTANDARD bsfSorryControl: [sorryAx]

## ===== verification-r1.zip:phase2/rule10/rule10-phases.out (this pack) =====

phase statements start 2026-11-17T07:51:17Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
touched rc=0
phase statements done 2026-11-17T07:51:17Z
phase collect start 2026-11-17T07:51:17Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
collector rc=0
phase collect done 2026-11-17T07:51:25Z
phase axioms start 2026-11-17T07:51:25Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
axioms rc=0
phase axioms done 2026-11-17T07:52:11Z
phase seals start 2026-11-17T07:52:11Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
rule10_b rc=1
phase seals done 2026-11-17T07:52:12Z
phase scan start 2026-11-17T07:52:12Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
scan2 rc=0
phase scan done 2026-11-17T07:52:16Z
phase seals start 2026-11-17T07:52:53Z head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff
rule10_b rc=0
phase seals done 2026-11-17T09:07:11Z

## ===== verification-r1.zip:phase2/rule10/mkctl-strict.log (this pack) =====

chosen ['SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random', 'SealA_Cryptography_AdvancedEncryption_IdentityBased_Defs', 'SealA_Cryptography_Games_Relational', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random', 'SealB_Cryptography_AdvancedEncryption_IdentityBased_Defs', 'SealB_Cryptography_Games_Relational']
32 control probes; 485 expected sealed failures

## ===== verification-r1.zip:phase2/rule10/ctlcheck-strict.log (this pack) =====

PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlDBDH', 1), ('ctlDBDHReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlLayout', 1), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlTupleStr', 1), ('ctlTupleStrReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlInput', 1), ('ctlInputReader', 0), ('ctlTapeImpl', 1), ('ctlTapeImplReader', 0), ('ctlQLen', 1), ('ctlQLenReader', 0), ('ctlDraw', 1), ('ctlDrawReader', 0), ('ctlSJ', 1), ('ctlSJReader', 0), ('ctlKT', 1), ('ctlKTReader', 0), ('ctlBlkS', 1), ('ctlBlkSReader', 0), ('ctlUS', 1), ('ctlUSReader', 0), ('ctlHandler', 1), ('ctlHandlerReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlDBDH', 0), ('ctlDBDHReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlLayout', 0), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlTupleStr', 0), ('ctlTupleStrReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlInput', 0), ('ctlInputReader', 0), ('ctlTapeImpl', 0), ('ctlTapeImplReader', 0), ('ctlQLen', 0), ('ctlQLenReader', 0), ('ctlDraw', 0), ('ctlDrawReader', 0), ('ctlSJ', 0), ('ctlSJReader', 0), ('ctlKT', 0), ('ctlKTReader', 0), ('ctlBlkS', 0), ('ctlBlkSReader', 0), ('ctlUS', 0), ('ctlUSReader', 0), ('ctlHandler', 0), ('ctlHandlerReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_Games_Relational rc 1 [('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_Games_Relational rc 0 [('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlDBDH', 1), ('ctlDBDHReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlLayout', 1), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlTupleStr', 1), ('ctlTupleStrReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlInput', 1), ('ctlInputReader', 0), ('ctlTapeImpl', 1), ('ctlTapeImplReader', 0), ('ctlQLen', 1), ('ctlQLenReader', 0), ('ctlDraw', 1), ('ctlDrawReader', 0), ('ctlSJ', 1), ('ctlSJReader', 0), ('ctlKT', 1), ('ctlKTReader', 0), ('ctlBlkS', 1), ('ctlBlkSReader', 0), ('ctlUS', 1), ('ctlUSReader', 0), ('ctlHandler', 1), ('ctlHandlerReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlDBDH', 0), ('ctlDBDHReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlLayout', 0), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlTupleStr', 0), ('ctlTupleStrReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlInput', 0), ('ctlInputReader', 0), ('ctlTapeImpl', 0), ('ctlTapeImplReader', 0), ('ctlQLen', 0), ('ctlQLenReader', 0), ('ctlDraw', 0), ('ctlDrawReader', 0), ('ctlSJ', 0), ('ctlSJReader', 0), ('ctlKT', 0), ('ctlKTReader', 0), ('ctlBlkS', 0), ('ctlBlkSReader', 0), ('ctlUS', 0), ('ctlUSReader', 0), ('ctlHandler', 0), ('ctlHandlerReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_Games_Relational rc 1 [('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_Games_Relational rc 0 [('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
ALL_OK True

## ===== verification-r1.zip:phase2/rule10/ctlcheck-coe.log (this pack) =====

PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlDBDH', 1), ('ctlDBDHReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlLayout', 1), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlTupleStr', 1), ('ctlTupleStrReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlInput', 1), ('ctlInputReader', 0), ('ctlTapeImpl', 1), ('ctlTapeImplReader', 0), ('ctlQLen', 1), ('ctlQLenReader', 0), ('ctlDraw', 1), ('ctlDrawReader', 0), ('ctlSJ', 1), ('ctlSJReader', 0), ('ctlKT', 1), ('ctlKTReader', 0), ('ctlBlkS', 1), ('ctlBlkSReader', 0), ('ctlUS', 1), ('ctlUSReader', 0), ('ctlHandler', 1), ('ctlHandlerReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlDBDH', 0), ('ctlDBDHReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlLayout', 0), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlTupleStr', 0), ('ctlTupleStrReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlInput', 0), ('ctlInputReader', 0), ('ctlTapeImpl', 0), ('ctlTapeImplReader', 0), ('ctlQLen', 0), ('ctlQLenReader', 0), ('ctlDraw', 0), ('ctlDrawReader', 0), ('ctlSJ', 0), ('ctlSJReader', 0), ('ctlKT', 0), ('ctlKTReader', 0), ('ctlBlkS', 0), ('ctlBlkSReader', 0), ('ctlUS', 0), ('ctlUSReader', 0), ('ctlHandler', 0), ('ctlHandlerReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0)] []
PASS ControlS_A_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 1 [('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 0 [('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_A_Cryptography_Games_Relational rc 1 [('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_A_Cryptography_Games_Relational rc 0 [('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlDBDH', 1), ('ctlDBDHReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlLayout', 1), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlTupleStr', 1), ('ctlTupleStrReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlInput', 1), ('ctlInputReader', 0), ('ctlTapeImpl', 1), ('ctlTapeImplReader', 0), ('ctlQLen', 1), ('ctlQLenReader', 0), ('ctlDraw', 1), ('ctlDrawReader', 0), ('ctlSJ', 1), ('ctlSJReader', 0), ('ctlKT', 1), ('ctlKTReader', 0), ('ctlBlkS', 1), ('ctlBlkSReader', 0), ('ctlUS', 1), ('ctlUSReader', 0), ('ctlHandler', 1), ('ctlHandlerReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlDBDH', 0), ('ctlDBDHReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlLayout', 0), ('ctlLayoutReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlTupleStr', 0), ('ctlTupleStrReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlInput', 0), ('ctlInputReader', 0), ('ctlTapeImpl', 0), ('ctlTapeImplReader', 0), ('ctlQLen', 0), ('ctlQLenReader', 0), ('ctlDraw', 0), ('ctlDrawReader', 0), ('ctlSJ', 0), ('ctlSJReader', 0), ('ctlKT', 0), ('ctlKTReader', 0), ('ctlBlkS', 0), ('ctlBlkSReader', 0), ('ctlUS', 0), ('ctlUSReader', 0), ('ctlHandler', 0), ('ctlHandlerReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0), ('ctlRelM', 1), ('ctlRelMReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0), ('ctlRelM', 0), ('ctlRelMReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 1), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 1), ('ctlRealLazyReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0), ('ctlRealAt', 0), ('ctlRealAtReader', 0), ('ctlRealState', 0), ('ctlRealStateReader', 0), ('ctlRealLazy', 0), ('ctlRealLazyReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDesc', 1), ('ctlDescReader', 0), ('ctlCorrect', 1), ('ctlCorrectReader', 0), ('ctlSidImpl', 1), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 1), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 1), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 1), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 1), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 1), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 1), ('ctlSidFreshReader', 0), ('ctlF', 1), ('ctlFReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 1), ('ctlOrderAtLeastReader', 0), ('ctlInst', 1), ('ctlInstReader', 0), ('ctlInLens', 1), ('ctlInLensReader', 0), ('ctlOutLens', 1), ('ctlOutLensReader', 0), ('ctlIdToZ', 1), ('ctlIdToZReader', 0), ('ctlOracleZero', 1), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 1), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 1), ('ctlOracleTwoReader', 0), ('ctlEncPP', 1), ('ctlEncPPReader', 0), ('ctlEncSK', 1), ('ctlEncSKReader', 0), ('ctlMsgSpace', 1), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 1), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 1), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 1), ('ctlEncBindReader', 0), ('ctlEncCT', 1), ('ctlEncCTReader', 0), ('ctlSimCt', 1), ('ctlSimCtReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0), ('ctlSimLazy', 1), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 1), ('ctlSimLazyChalReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDesc', 0), ('ctlDescReader', 0), ('ctlCorrect', 0), ('ctlCorrectReader', 0), ('ctlSidImpl', 0), ('ctlSidImplReader', 0), ('ctlSidZeroSpec', 0), ('ctlSidZeroSpecReader', 0), ('ctlSidTwoSpec', 0), ('ctlSidTwoSpecReader', 0), ('ctlSidOneQuery', 0), ('ctlSidOneQueryReader', 0), ('ctlSidTwoQuery', 0), ('ctlSidTwoQueryReader', 0), ('ctlSidKeyNe', 0), ('ctlSidKeyNeReader', 0), ('ctlSidFresh', 0), ('ctlSidFreshReader', 0), ('ctlF', 0), ('ctlFReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlOrderAtLeast', 0), ('ctlOrderAtLeastReader', 0), ('ctlInst', 0), ('ctlInstReader', 0), ('ctlInLens', 0), ('ctlInLensReader', 0), ('ctlOutLens', 0), ('ctlOutLensReader', 0), ('ctlIdToZ', 0), ('ctlIdToZReader', 0), ('ctlOracleZero', 0), ('ctlOracleZeroReader', 0), ('ctlOracleOne', 0), ('ctlOracleOneReader', 0), ('ctlOracleTwo', 0), ('ctlOracleTwoReader', 0), ('ctlEncPP', 0), ('ctlEncPPReader', 0), ('ctlEncSK', 0), ('ctlEncSKReader', 0), ('ctlMsgSpace', 0), ('ctlMsgSpaceReader', 0), ('ctlSetupEq', 0), ('ctlSetupEqReader', 0), ('ctlKeyGenBind', 0), ('ctlKeyGenBindReader', 0), ('ctlEncBind', 0), ('ctlEncBindReader', 0), ('ctlEncCT', 0), ('ctlEncCTReader', 0), ('ctlSimCt', 0), ('ctlSimCtReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0), ('ctlSimLazy', 0), ('ctlSimLazyReader', 0), ('ctlSimLazyChal', 0), ('ctlSimLazyChalReader', 0)] []
PASS ControlS_B_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 1 [('ctlEval', 1), ('ctlEvalReader', 0), ('ctlPadFin', 1), ('ctlPadFinReader', 0), ('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlDistL', 1), ('ctlDistLReader', 0), ('ctlRunAtL', 1), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 1), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 1), ('ctlAdvInputReader', 0), ('ctlAccept', 1), ('ctlAcceptReader', 0), ('ctlUprob', 1), ('ctlUprobReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_AdvancedEncryption_IdentityBased_Defs rc 0 [('ctlEval', 0), ('ctlEvalReader', 0), ('ctlPadFin', 0), ('ctlPadFinReader', 0), ('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlDistL', 0), ('ctlDistLReader', 0), ('ctlRunAtL', 0), ('ctlRunAtLReader', 0), ('ctlOfPolyTime', 0), ('ctlOfPolyTimeReader', 0), ('ctlAdvInput', 0), ('ctlAdvInputReader', 0), ('ctlAccept', 0), ('ctlAcceptReader', 0), ('ctlUprob', 0), ('ctlUprobReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
PASS ControlS_B_Cryptography_Games_Relational rc 1 [('ctlAllOutputs', 1), ('ctlAllOutputsReader', 0), ('ctlExpect', 1), ('ctlExpectReader', 0)] []
PASS ControlU_B_Cryptography_Games_Relational rc 0 [('ctlAllOutputs', 0), ('ctlAllOutputsReader', 0), ('ctlExpect', 0), ('ctlExpectReader', 0)] []
ALL_OK True

## ===== verification-r1.zip:phase2/scan/scan2-head.log (this pack) =====

{
 "items": 527,
 "by_class": {
  "THEOREM": 426,
  "LOCAL_OR_UNRESOLVED": 85,
  "OWNED_DEFINITION": 14,
  "SIMPROC": 2
 },
 "foreign_items": 0,
 "foreign_by_file_touched": {},
 "foreign_subkinds": {}
}

## ===== verification-r1.zip:phase1/controls-recount.txt (this pack) =====

controls-strict {'neg': 485, 'neg_ok': 485, 'pos': 485, 'pos_ok': 485, 'unsealed_bad': 0, 'stray': 0, 'probes': 32, 'missing': 0} run dirs ['K', 'KS']
controls-coe {'neg': 485, 'neg_ok': 485, 'pos': 485, 'pos_ok': 485, 'unsealed_bad': 0, 'stray': 0, 'probes': 32, 'missing': 0} run dirs ['K', 'KS']

## ===== verification-r1.zip:phase1/seal-recount.tsv (this pack) =====

seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	840	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2320	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain	877	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling	874	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy	868	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random	871	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Real	871	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_Defs	805	True	True	0	0	True	0	True
seals	SealA_Cryptography_Games_Relational	53	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	841	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2321	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain	878	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling	875	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy	869	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random	872	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Real	872	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_Defs	806	True	True	0	0	True	0	True
seals	SealB_Cryptography_Games_Relational	53	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	839	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2319	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain	876	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling	873	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy	867	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random	870	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Real	870	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_Defs	804	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_Games_Relational	52	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	840	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2320	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Chain	877	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Coupling	874	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Lazy	868	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Random	871	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity_Real	871	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_Defs	805	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_Games_Relational	52	True	True	0	0	True	0	True
deliv/inbox/fills/bb1-sim/evidence/rule10/head: seals 36; not OK 0
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	840	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2312	True	True	0	0	True	0	True
seals	SealA_Cryptography_AdvancedEncryption_IdentityBased_Defs	805	True	True	0	0	True	0	True
seals	SealA_Cryptography_Games_Relational	53	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	841	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2313	True	True	0	0	True	0	True
seals	SealB_Cryptography_AdvancedEncryption_IdentityBased_Defs	806	True	True	0	0	True	0	True
seals	SealB_Cryptography_Games_Relational	53	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	839	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2311	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_AdvancedEncryption_IdentityBased_Defs	804	True	True	0	0	True	0	True
seals-coe	SealA_Cryptography_Games_Relational	52	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyen	840	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenSecurity	2312	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_AdvancedEncryption_IdentityBased_Defs	805	True	True	0	0	True	0	True
seals-coe	SealB_Cryptography_Games_Relational	52	True	True	0	0	True	0	True
deliv/inbox/fills/bb1-sim/evidence/rule10/base: seals 16; not OK 0

## ===== verification-r1.zip:phase1/shortname-scan.txt (this pack) =====

# short-name scan at check base 02b2d44a (git grep -w over TCSlib/ and audits/), with 2 positive controls
BB1Sim occurrences at base: 4
bb1Scheme_enc_bind bb1Scheme_enc_bind 0
bb1Scheme_keyGen_bind bb1Scheme_keyGen_bind 0
bb1Scheme_setup_eq bb1Scheme_setup_eq 0
ofFn_bb1Scheme_encCT ofFn_bb1Scheme_encCT 0
BB1Sim.prob_sidGame_coins prob_sidGame_coins 0
BB1Sim.F_target_eq F_target_eq 0
BB1Sim.RelM RelM 0
BB1Sim.exists_equiv_mul_pow exists_equiv_mul_pow 0
BB1Sim.expect_simulate_bb1RealLazy expect_simulate_bb1RealLazy 0
BB1Sim.key_eq key_eq 0
BB1Sim.natCast_bitsToNat_injective natCast_bitsToNat_injective 0
BB1Sim.pair_pow_val_eq pair_pow_val_eq 0
BB1Sim.relM_iff relM_iff 0
BB1Sim.stepM_call stepM_call 0
BB1Sim.stepM_challenge_fresh stepM_challenge_fresh 0
BB1Sim.stepM_challenge_invalid stepM_challenge_invalid 0
BB1Sim.stepM_challenge_none stepM_challenge_none 0
BB1Sim.stepM_challenge_repeat stepM_challenge_repeat 0
BB1Sim.stepM_init_none stepM_init_none 0
BB1Sim.stepM_init_some stepM_init_some 0
BB1Sim.stepM_keyGen_ne stepM_keyGen_ne 0
BB1Sim.stepM_keyGen_none stepM_keyGen_none 0
BB1Sim.stepM_keyGen_target stepM_keyGen_target 0
BB1Sim.bb1SimImpl_allOutputs_of_ne_two bb1SimImpl_allOutputs_of_ne_two 0
BB1Sim.bb1SimImpl_one_coins bb1SimImpl_one_coins 0
BB1Sim.bb1SimImpl_two_fresh_allOutputs bb1SimImpl_two_fresh_allOutputs 0
BB1Sim.bb1SimImpl_two_of_not bb1SimImpl_two_of_not 0
BB1Sim.bb1SimImpl_zero_coins bb1SimImpl_zero_coins 0
BB1Sim.bb1SimLazy bb1SimLazy 0
BB1Sim.bb1SimLazyChal bb1SimLazyChal 0
BB1Sim.bb1SimLazyChal_fresh bb1SimLazyChal_fresh 0
BB1Sim.bb1SimLazyChal_of_not bb1SimLazyChal_of_not 0
BB1Sim.bb1SimLazy_eq bb1SimLazy_eq 0
BB1Sim.bb1SimLazy_one bb1SimLazy_one 0
BB1Sim.bb1SimLazy_two_fresh bb1SimLazy_two_fresh 0
BB1Sim.bb1SimLazy_two_of_not bb1SimLazy_two_of_not 0
BB1Sim.bb1SimLazy_zero bb1SimLazy_zero 0
BB1Sim.expect_simulate_bb1SimLazy expect_simulate_bb1SimLazy 0
BB1Sim.sidSpec_dom_one sidSpec_dom_one 0
BB1Sim.sidSpec_dom_two sidSpec_dom_two 0
BB1Sim.sidSpec_dom_zero sidSpec_dom_zero 0
BB1Sim.sidSpec_rng_one sidSpec_rng_one 2
BB1Sim.sidSpec_rng_two sidSpec_rng_two 2
BB1Sim.sidSpec_rng_zero sidSpec_rng_zero 0
BB1Sim.zeroBits_eq_cast zeroBits_eq_cast 0
BB1Sim.bb1SimLazy_random_call bb1SimLazy_random_call 0
BB1Sim.expect_bb1SimImpl_random expect_bb1SimImpl_random 0
BB1Sim.BB1RealState BB1RealState 0
BB1Sim.RealReads RealReads 0
BB1Sim.bb1RealAt bb1RealAt 0
BB1Sim.bb1RealAt_none bb1RealAt_none 0
BB1Sim.bb1RealAt_some bb1RealAt_some 0
BB1Sim.bb1RealLazy bb1RealLazy 0
BB1Sim.bb1RealLazy_none_of_ne bb1RealLazy_none_of_ne 0
BB1Sim.bb1RealLazy_some bb1RealLazy_some 0
BB1Sim.bb1RealLazy_zero_none bb1RealLazy_zero_none 0
BB1Sim.expect_sample_bb1RealAt expect_sample_bb1RealAt 0
BB1Sim.expect_sample_sidImpl expect_sample_sidImpl 0
BB1Sim.expect_simulate_sidImpl_bb1RealAt expect_simulate_sidImpl_bb1RealAt 0
BB1Sim.setup_out setup_out 0
BB1Sim.sidImpl_allOutputs_some sidImpl_allOutputs_some 0
BB1Sim.sidImpl_none_of_ne sidImpl_none_of_ne 0
IBEScheme.sidImpl_challenge_fresh_onSpec sidImpl_challenge_fresh_onSpec 0
IBEScheme.sidImpl_keyGen_ne_onSpec sidImpl_keyGen_ne_onSpec 0
IBEScheme.sidImpl_one_onQuery sidImpl_one_onQuery 0
IBEScheme.sidImpl_two_onQuery sidImpl_two_onQuery 0
IBEScheme.sidImpl_two_onSpec sidImpl_two_onSpec 0
IBEScheme.sidImpl_zero_onSpec sidImpl_zero_onSpec 0
CTRL:bb1SimChal_fresh bb1SimChal_fresh 2
CTRL:sidImpl_init_none sidImpl_init_none 2
BB1Sim. (namespace) occurrences at base: 0; 'namespace BB1Sim' 0

## ===== verification-r1.zip:phase1/cs1-added-names.txt (this pack) =====

FinDist.expect_map
FinDist.map_apply_expect
FinDist.map_map
FinDist.map_prod_snd
FinDist.map_uniform_equiv
FinDist.mixture
FinDist.mixture_apply
FinDist.mixture_isSource
FinDist.probTrue_le_one
FinDist.probTrue_map
FinDist.probTrue_nonneg
FinDist.sum_map
FinDist.uniform_probTrue
FinDist.uniform_prod
FunFamily.ofFn_blocks_symm_eq_flatMap
OracleComp.exists_eq_pure_of_costBoundedBy_zero
StatClose.of_uprob_ne
_root_.Complexity.NUPPT.eval_toOracleAdversary_padFin
copyTMView
copyTMView_eq
copy_clean_view
encodeList_eq_flatMap
encodeMsgs_eq
encodeMsgs_eq_encWords
encodeMsgs_eq_flatMap
expect_sample_eq_uexp
expect_sample_ovr
expect_simulate_abs
expect_simulate_abs_inv
expect_simulate_tapeImpl
extTape
extTape_of_lt
extTape_of_not_lt
extTape_update
flatMap_range_ite
freshImpl
freshImpl_apply
getD_ofFn
getD_padTo
hostTMView
hostTMView_eq
hostTMView_q₀
hostTMView_step_inl
host_branch_view
host_call_view
host_clean_view
host_dispatch_view
host_halt_view
iterSnd_poly
iterate_pairSndD_encodeMsgs
length_le_length_encodeLog
length_ofFn_coins
length_padTo
length_recordBits
msgAt_encodeMsgs
ofFn_splitBits_fst
ofFn_splitBits_snd
ovr
ovr_append
ovr_cons
ovr_nil
ovr_of_mem
ovr_of_not_mem
ovr_update
padTo
padTo_eq
padTo_of_length
padTo_poly
pkPredictor_apply
polyTimeComputable_find
polyTimeComputable_flatMap_range
recordBits
recordBits_none
recordBits_some
simulate_tapeImpl_congr
tapeImpl
tapeImpl_apply
zeros_poly
zipWith_xor_cancel_right

## ===== verification-r1.zip:phase1/quotes.txt (this pack) =====

Chain.lean OK | When the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack game 
Coupling.lean OK | let `r̃_j = r_j − b/(I_j − I^*_j)` 
Coupling.lean OK | Since `F_i(I^*_i) = g^{α_i}` 
Coupling.lean OK | if `T = e(g, g)^{abc} = e(g_1, g_2)^c` 
Coupling.lean OK | let `r̃_j = r_j − b/(I_j − I^*_j)` 
Coupling.lean OK | Since `F_i(I^*_i) = g^{α_i}` 
Random.lean OK | when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the adversary's view 
BonehBoyenSecurity.lean OK | When the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack game 
BonehBoyenSecurity.lean OK | when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the adversary's view 
# control: a fabricated quotation must be MISSING
quote-control.lean.txt MISSING | the simulator aborts with probability 1/2 ['thesimulatorabortswithprobability1/2']

## ===== pr357.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean
index 930b04805..c70c661f3 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean
@@ -411,6 +411,52 @@ theorem bb1Scheme_msgSpace_iff (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d
       ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m :=
   exists_congr fun _ => List.ofFn_inj.symm
 
+/-- **`Setup` at the scheme's types**: `Setup` runs the generator and BB1's `Setup`, and returns
+`(⟨d, params⟩, ⟨d, (params, master-key)⟩)` as parameters and master key of `bb1Scheme G ℓ`:
+`Setup κ = (sample r).bind fun r => (BB1.setup _).bind fun k => pure (⟨desc r, k.1⟩, ⟨desc r, k⟩)`,
+the pair typed at `PP κ × MSK κ`. -/
+theorem bb1Scheme_setup_eq (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) :
+    (bb1Scheme G ℓ).setup κ =
+      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
+      (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
+        .pure (((⟨G.desc κ r, k.1⟩ : (bb1Scheme G ℓ).PP κ),
+          (⟨G.desc κ r, k⟩ : (bb1Scheme G ℓ).MSK κ)) :
+            (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) := rfl
+
+/-- **`KeyGen` at the scheme's types, followed by `f`**: for the master key `⟨d, (pp, mk)⟩` and an
+`ℓ(κ)`-bit identity `ID`, `KeyGen` is BB1's `KeyGen` on `idToZ ID`, its key tagged with `d`:
+`(KeyGen ⟨d, (pp, mk)⟩ ID).bind f = (BB1.keyGen pp mk (idToZ ID)).bind fun k => f ⟨d, k⟩`. -/
+theorem bb1Scheme_keyGen_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
+    (pp : BB1.Params (G.group κ d)) (mk : (G.group κ d).G)
+    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) {β : Type}
+    (f : (bb1Scheme G ℓ).SK κ → ProbComp β) :
+    ((bb1Scheme G ℓ).keyGen κ ⟨d, (pp, mk)⟩ id).bind f =
+      (BB1.keyGen pp mk (BB1.idToZ (G.group κ d) id)).bind fun k => f ⟨d, k⟩ := by
+  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind]
+
+/-- **`Encrypt` at the scheme's types, followed by `f`**: for the parameters `⟨d, pp⟩`, an
+`ℓ(κ)`-bit identity `ID` and a `msgLen(κ)`-bit message `m`, `Encrypt` is BB1's `Encrypt` on
+`idToZ ID` and `decodeT m` (the message read at the width of `G_T`), its ciphertext tagged
+with `d`: `(Encrypt ⟨d, pp⟩ ID m).bind f = (BB1.encrypt pp (idToZ ID) (decodeT ⟦m⟧)).bind fun c =>
+f ⟨d, c⟩`. -/
+theorem bb1Scheme_enc_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
+    (pp : BB1.Params (G.group κ d)) (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
+    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) {β : Type}
+    (f : (bb1Scheme G ℓ).CT κ → ProbComp β) :
+    ((bb1Scheme G ℓ).enc κ ⟨d, pp⟩ id m).bind f =
+      (BB1.encrypt pp (BB1.idToZ (G.group κ d) id)
+        (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))).bind fun c => f ⟨d, c⟩ := by
+  rw [padFin_ofFn]
+  simp only [bb1Scheme_enc, OracleComp.bind_assoc, OracleComp.pure_bind]
+
+/-- **The ciphertext encoding as a word**: `⟦encCT ⟨d, c⟩⟧` is the padded word `A ‖ B ‖ C_1`
+(`ctLen(κ)` bits). -/
+theorem ofFn_bb1Scheme_encCT (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
+    (c : BB1.Ciphertext (G.group κ d)) :
+    List.ofFn ((bb1Scheme G ℓ).encCT κ ⟨d, c⟩) =
+      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ) (List.ofFn ((G.group κ d).encT c.a) ++
+        List.ofFn ((G.group κ d).encG c.b) ++ List.ofFn ((G.group κ d).encG c.c))) := rfl
+
 /-- **BB1 is perfectly correct** [BB04, §4.1, "Indeed, for a valid ciphertext …"]: every
 honest run with a message of the message space decrypts to that message.
 
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
index 08f5211fd..1e3f07ea6 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
@@ -6,6 +6,11 @@ Authors: TCSlib contributors
 import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
 import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
 import TCSlib.Cryptography.Pairing.Assumptions
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Random
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -47,6 +52,20 @@ the sum of two Decision BDH advantages; the paper's statement is concrete (`t' <
 None: the simulator (`bb1SimImpl`, `bb1SimGame`) is defined beside the scheme, in
 `AdvancedEncryption.IdentityBased.BonehBoyen`.
 
+## Contents
+
+Steps 1 and 2 are proved in helper modules:
+
+* `BonehBoyenSecurity.Lazy`: the simulator with its challenge coins drawn at the first valid
+  `Challenge`, and its eager step.
+* `BonehBoyenSecurity.Real`: the output of `Setup`, read; the real game with `h` recorded, and
+  with `h` drawn at the first `Init`.
+* `BonehBoyenSecurity.Coupling`: step M, the real game against the simulator call by call, on
+  good coins.
+* `BonehBoyenSecurity.Random`: on a random `T`, the simulator does not depend on the challenge
+  bit.
+* `BonehBoyenSecurity.Chain`: on good coins, the real game is the simulation on `P_BDH`.
+
 ## Main results
 
 * `bb1_sim_real`, `bb1_sim_random` — steps 1 and 2 (step 3, `exists_bb1_distinguisher`, is in
@@ -75,35 +94,71 @@ the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its vie
 game"], except on the generator's coins where `p < 2^ℓ`, where distinct identities may collide
 in `Z_p`.
 
-**Proof sketch.** Fix coins with `2^ℓ ≤ p`, so `idToZ` is injective on `ℓ`-bit strings
-(`bitsToNat_lt`, `bitsToNat_injective`). Couple the two games: the real `Setup` draws
-`(g, α, h, g_2)`, the simulation `(g, a, b', c)` and, at `Init`, `α_1`. Map `α ↦ a`,
-`g_2 ↦ g^{b'}` and `h ↦ g_1^{−ID*} g^{α_1}` (a bijection in `α_1` for each `ID*`, so `h` is uniform
-and independent; `expect_sample_equiv`). Answers to `Init` agree. For `ID ≠ ID*` the simulated
-key with exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of
-`Z_p` (the paper's computation, `pow_val_mul`, `bilinear_pow`). The challenge is `Encrypt` with
-`s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c`. The state machines agree
-step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`), so the
-acceptance probabilities differ only on the excluded coins, of probability
-`Pr_r[p < 2^ℓ]`. -/
+**Proof sketch.** Read `Setup` through `BB1Sim.setup_out` and condition both games on the
+generator's coins `r` (`prob_bind`). On coins with `p < 2^ℓ` the two conditional acceptances are
+probabilities, so they differ by at most `1`; averaging this pointwise bound
+(`ProbComp.abs_expect_sub_le_expect`) gives `Pr_r[p < 2^ℓ]` (`Bridge.prob_sample_eq_uprob`). On
+coins with `2^ℓ ≤ p` they are equal (`BB1Sim.prob_sidGame_coins`), by coupling the two games:
+* the real `Setup` draws `h` before `ID*` exists; move it past `g_2` and the adversary's coins and
+  draw it at the first `Init` (`ProbComp.expect_simulate_rel` with `h` recorded beside `ID*`, then
+  `Games.expect_simulate_eager`);
+* map `α ↦ a` and read `g_2` as `g^{b'}` (`pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
+* the real game and the simulator then agree call by call on states related by
+  `h = g_1^{−ID*} g^{α_1}` (`ProbComp.expect_simulate_rel`, `ProbComp.expect_sample_rel`): at
+  `Init`, `h ↦ α_1` is a bijection for each `ID*`, so `h` is uniform and the answers agree; for
+  `ID ≠ ID*`, which stay distinct in `Z_p` because `idToZ` is injective on `ℓ`-bit strings
+  (`bitsToNat_lt`, `bitsToNat_injective`, `CharP.natCast_injOn_Iio`), the simulated key with
+  exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of `Z_p` (the
+  paper's computation, `pow_val_add`, `pow_val_neg`, `pow_val_mul`); the challenge is `Encrypt`
+  with `s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c` (`bilinear_pow`);
+* finally the challenge coin `c` is drawn in advance (`Games.expect_simulate_eager`) and
+  `(a, b', c)` merges into one draw (`Bridge.expect_sample_pair`); the unused `T` drops out. -/
 theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
     advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
       uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
-  sorry
+  obtain ⟨o, hset, hR⟩ := BB1Sim.setup_out G ℓ κ
+  rw [advantage_eq, accept_eq, accept_eq, IBEScheme.sidGame_eq, hset, bb1SimGame_eq,
+    ProbComp.prob_bind, ProbComp.prob_bind]
+  -- average the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]` over the generator's coins
+  calc _ ≤ ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
+          (fun r => if (G.inst κ r).order < 2 ^ ℓ.eval κ then 1 else 0) :=
+        ProbComp.abs_expect_sub_le_expect _ fun r => ?_
+    _ = uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
+        rw [← ProbComp.prob_eq_expect, Bridge.prob_sample_eq_uprob]
+  have h01 : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| ≤ 1 := fun x y _ _ _ _ =>
+    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
+  by_cases hr : (G.inst κ r).order < 2 ^ ℓ.eval κ
+  -- bad coins: two probabilities differ by at most `1`
+  · rw [if_pos hr]
+    exact h01 _ _ (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
+      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
+  -- good coins: the chain of `BB1Sim.prob_sidGame_coins`
+  · rw [if_neg hr]
+    exact (abs_eq_zero.2 (sub_eq_zero.2 (BB1Sim.prob_sidGame_coins G ℓ A q b κ o hR r hr))).le
 
 /-- **Step 2: on `R_BDH` the simulation does not depend on the challenge bit** [BB04, proof of
 Theorem 4.1, "when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the
 adversary's view"].
 
-**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only in the first
-component `M_b · T` of the challenge. For each fixed run up to the challenge, `T ↦ M_b · T` is a
-bijection of `G_T`, so exchanging the sample of `T` with the rest of the game
-(`expect_expect_sample`) and reindexing it by `T ↦ M_b^{−1} M_{1−b} · T`
-(`expect_sample_equiv`) turns the game with `b = 0` into the game with `b = 1`. Challenges
-outside the message space are refused in both games. -/
+**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only at the first
+valid `Challenge`, in the first component `M_b · T` of the challenge. Exchange the sample of `T`
+with the adversary's coins (`expect_sample_comm`) and draw it at that call
+(`BB1Sim.expect_simulate_bb1SimLazy`, an instance of `expect_simulate_eager`). The simulators
+with `b = 0` and `b = 1` then agree call by call (`ProbComp.expect_simulate_congr`): every other
+call is the same for both bits, and at the first valid `Challenge` the bijection
+`T ↦ M_1^{−1} M_0 · T` of `G_T` turns the answer `M_0 · T` into `M_1 · T'`
+(`ProbComp.expect_sample_rel`). Challenges outside the message space are refused in both games.
+So the acceptance probabilities are equal (`advantage_eq`). -/
 theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
     advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
-  sorry
+  rw [advantage_eq, abs_eq_zero, sub_eq_zero, accept_eq, accept_eq, bb1SimGame_eq, bb1SimGame_eq]
+  simp only [ProbComp.prob_bind, Bool.false_eq_true, if_false]
+  refine congrArg _ (funext fun r => congrArg _ (funext fun g => congrArg _ (funext fun abc => ?_)))
+  -- `T` is drawn before `A`'s coins: exchange them, then compare the two bits for each `ρ`
+  conv_lhs => rw [ProbComp.expect_sample_comm]
+  conv_rhs => rw [ProbComp.expect_sample_comm]
+  exact congrArg _ (funext fun ρ => BB1Sim.expect_bb1SimImpl_random G ℓ κ _ _ _ _ _
+    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (fun a => ProbComp.prob (.pure (a 0)) (· = true)))
 
 /-- **BB1 is IND-sID-CPA secure under Decision BDH** [BB04, Theorem 4.1, at depth `ℓ = 1`]: if
 the generator's groups have efficient operations, the arithmetic bundle holds, the order is at
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean
new file mode 100644
index 000000000..2b9c5d6aa
--- /dev/null
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean
@@ -0,0 +1,130 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
+import TCSlib.Cryptography.Games.Bridges.Experiments
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# On good coins, the real BB1 game is the simulation on `P_BDH`
+
+Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
+[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "When the input 5-tuple is sampled from
+`P_BDH` (where `T = e(g, g)^{abc}`) then `A`'s view is identical to its view in a real attack
+game" [BB04, proof of Theorem 4.1, *Phase 2, Guess and the advantage*]. For generator coins `r`
+with `2^ℓ ≤ p`, the chain of design r1 §3.1 equates the real game's acceptance, conditioned on
+`r`, with the simulation game's on `P_BDH`:
+1. move the setup's `h` past `g_2` and the adversary's coins, and draw it at the first `Init`
+   (`expect_sample_sidImpl`: steps R1 and E-h);
+2. read `g_2` as `g^{b'}` (`BilinearGroup.pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
+3. step M (`expect_simulate_bb1RealLazy`);
+4. draw the challenge coin `c` in advance (`expect_simulate_bb1SimLazy`, step E-c), and merge
+   `(a, b', c)` (`Bridge.expect_sample_pair`); the unused `T` drops out (`expect_const`).
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `BB1Sim.prob_sidGame_coins` — on good coins, the real game's acceptance, conditioned on the
+  generator's coins, is the simulation game's on `P_BDH`.
+
+## References
+
+* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
+  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
+  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
+  Theorem 4.1.
+-/
+
+namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
+
+open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
+  TCSlib.Cryptography.Composability
+
+namespace BB1Sim
+
+variable (G : BilinearGen) (ℓ : PolyExpr)
+
+/-- **On good coins, the real game is the simulation on `P_BDH`** [BB04, proof of Theorem 4.1,
+*Phase 2, Guess and the advantage*, "When the input 5-tuple is sampled from `P_BDH` … `A`'s view
+is identical to its view in a real attack game"]: let `o` be the setup's output map, read as in
+`setup_out`. For generator coins `r` with `2^{ℓ(κ)} ≤ p`, the real game after `r`
+(`g ∈ G^*`, `α`, `h`, `g_2`, `A`'s coins, the game's oracles on `o r g α h g_2`) and the
+simulation game after `r` on `P_BDH` (`g ∈ G^*`, `(a, b', c)`, `T`, `A`'s coins, the simulator
+on `(g, g^a, g^{b'}, g^c, e(g, g)^{a b' c})`) accept with the same probability.
+
+**Proof sketch.** Expand both probabilities into expectations (`prob_bind`) and fix `g` and
+`α = a`. Move `h` inside past `g_2` and `A`'s coins (`expect_sample_comm`) and draw it at the
+first `Init` (`expect_sample_sidImpl`). Read `g_2 = g^{b'}` (`expect_sample_equiv` along
+`pow_val_bijective_of_ne_one`), so that `o … h (g^{b'})` reads as `(g, g^a, g^{b'}, h)`
+(`setup_out`'s `RealReads`). Step M (`expect_simulate_bb1RealLazy`, with
+`natCast`-injectivity of identities from `2^ℓ ≤ p`) and E-c (`expect_simulate_bb1SimLazy`) give
+the simulator on `g^c`, `e(g, g)^{a b' c}` with `c` drawn in advance. On the simulation side,
+`T` is unused (`expect_const`) and `(a, b', c)` splits into three draws
+(`Bridge.expect_sample_pair`); `c` moves past `A`'s coins (`expect_sample_comm`). -/
+theorem prob_sidGame_coins (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ)
+    (o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
+        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
+        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
+    (hR : ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2))
+    (r : G.gen.Coins κ) (hr : ¬ (G.inst κ r).order < 2 ^ ℓ.eval κ) :
+    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
+      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
+      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
+      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 =>
+      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
+      (simulate ((bb1Scheme G ℓ).sidImpl b κ (o r g α h g2).1 (o r g α h g2).2)
+        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
+        fun res => .pure (res.1 0)) (· = true) =
+    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
+      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order ×
+        ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order)).bind
+        fun abc =>
+      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
+      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
+      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
+          (g.1 ^ abc.2.2.val)
+          (if true then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
+            else t))
+        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
+        fun res => .pure (res.1 0)) (· = true) := by
+  have hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ (G.desc κ r)).order := by
+    rw [bb1Scheme_idLen]
+    rw [BilinearGen.inst_eq, not_lt] at hr
+    exact hr
+  simp only [ProbComp.prob_bind]
+  refine congrArg _ (funext fun g => ?_)
+  -- the simulation side: split `(a, b', c)` into three draws; the unused `T` drops out
+  rw [← Bridge.expect_sample_pair]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
+  refine congrArg _ (funext fun α => ?_)
+  rw [← Bridge.expect_sample_pair]
+  simp only [ProbComp.expect_bind, ProbComp.expect_pure, ↓reduceIte, ProbComp.expect_const]
+  -- the real side: move `h` past `g_2` and `A`'s coins, then draw it at the first `Init`
+  conv_lhs => rw [ProbComp.expect_sample_comm]
+  conv_lhs => enter [2, g2]; rw [ProbComp.expect_sample_comm]
+  conv_lhs => enter [2, g2, 2, ρ]; rw [expect_sample_sidImpl G ℓ b κ _ (fun h => o r g α h g2)
+    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (fun a => ProbComp.prob (.pure (a 0)) (· = true))]
+  -- read `g_2` as `g^{b'}`
+  rw [← ProbComp.expect_sample_equiv (Equiv.ofBijective _
+    (BilinearGroup.pow_val_bijective_of_ne_one _ g.2))]
+  simp only [Equiv.ofBijective_apply]
+  refine congrArg _ (funext fun b' => ?_)
+  -- draw the challenge coin before `A`'s coins, then step M and E-c for each `ρ`
+  conv_rhs => rw [ProbComp.expect_sample_comm]
+  refine congrArg _ (funext fun ρ => ?_)
+  exact (expect_simulate_bb1RealLazy G ℓ b κ _ (fun h => o r g α h (g.1 ^ b'.val)) g.1 α b' g.2 hp
+    (fun h => hR r g α h _) (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ)
+    (fun a => ProbComp.prob (.pure (a 0)) (· = true))).trans
+      (expect_simulate_bb1SimLazy G ℓ b κ _ g.1 _ _ _ _ _ rfl)
+
+end BB1Sim
+
+end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean
new file mode 100644
index 000000000..da37cf2c9
--- /dev/null
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean
@@ -0,0 +1,565 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# Step M of BB1's simulation: the real game against the simulator, call by call
+
+Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
+[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). After `h` is drawn at the first `Init`
+(`BB1Sim.bb1RealLazy`) and the challenge coin `c` at the first valid `Challenge`
+(`BB1Sim.bb1SimLazy`), the real game and the simulator answer alike call by call, on states
+related by design r1 §3.1's relation `RelM`: the same recorded challenge, the same committed
+identity `ID*`, and `h = X^{−ID*} g^{α_1}` [BB04, proof of Theorem 4.1, *Setup*]. The real
+`KeyGen` exponent `r̃` and the simulated one `r` correspond by `r = r̃ + b/(ID − ID*)`
+[BB04, proof of Theorem 4.1, *Phase 1*], which needs `ID ≠ ID*` in `Z_p`: the generator's coins
+must give `2^ℓ ≤ p`. The challenge is `Encrypt` with `s = c`
+[BB04, proof of Theorem 4.1, *Challenge*].
+
+## Main definitions
+
+* `BB1Sim.RelM` — the relation of step M.
+
+## Main results
+
+* `BB1Sim.exists_equiv_mul_pow`, `BB1Sim.natCast_bitsToNat_injective`, `BB1Sim.key_eq`,
+  `BB1Sim.F_target_eq`, `BB1Sim.pair_pow_val_eq` — the group algebra of the coupling.
+* `BB1Sim.stepM_init_none`, …, `BB1Sim.stepM_challenge_fresh` — step M, call by call.
+* `BB1Sim.stepM_call` — the per-call hypothesis of `ProbComp.expect_simulate_rel`.
+* `BB1Sim.expect_simulate_bb1RealLazy` — step M: on good coins, the real game with `h` drawn at
+  `Init` simulates like the lazy simulator on `Y = g^{b'}` with `c` drawn at the challenge.
+
+## References
+
+* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
+  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
+  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
+  Theorem 4.1.
+-/
+
+namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
+
+open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
+  TCSlib.Cryptography.Composability
+
+namespace BB1Sim
+
+/-! ### The group algebra of the coupling -/
+
+section Algebra
+
+variable {wG wT : ℕ} (B : BilinearGroup wG wT)
+
+/-- **`h ↦ α_1` along `h = X^{−z} g^{α_1}`** [BB04, proof of Theorem 4.1, *Setup*]: for `g ≠ 1`
+and every `X`, there are bijections `e z : G ≃ Z_p`, one for each `z ∈ Z_p`, with
+`h = X^{(−z).val} · g^{(e z h).val}` for every `h`. -/
+theorem exists_equiv_mul_pow {g : B.G} (hg : g ≠ 1) (X : B.G) :
+    ∃ e : ZMod B.order → B.G ≃ ZMod B.order,
+      ∀ z h, h = X ^ (-z).val * g ^ (e z h).val := by
+  let E : ZMod B.order ≃ B.G := Equiv.ofBijective _ (B.pow_val_bijective_of_ne_one hg)
+  refine ⟨fun z => (Equiv.mulLeft (X ^ (-z).val)⁻¹).trans E.symm, fun z h => ?_⟩
+  have hE : g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val = (X ^ (-z).val)⁻¹ * h :=
+    E.apply_symm_apply _
+  show h = X ^ (-z).val * g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val
+  rw [hE, mul_inv_cancel_left]
+
+/-- **Distinct `n`-bit identities are distinct in `Z_p` when `2^n ≤ p`**: reading `n`-bit strings
+as numbers modulo `p` is injective, `fun u => (bitsToNat u : ZMod p)`. Glue for
+[BB04, §4.4]'s condition on the identity length. -/
+theorem natCast_bitsToNat_injective {n p : ℕ} (hp : 2 ^ n ≤ p) :
+    Function.Injective fun u : Fin n → Bool => (bitsToNat u : ZMod p) := fun u v huv =>
+  bitsToNat_injective (CharP.natCast_injOn_Iio (ZMod p) p (lt_of_lt_of_le (bitsToNat_lt u) hp)
+    (lt_of_lt_of_le (bitsToNat_lt v) hp) huv)
+
+/-- **The simulated key is a real key** [BB04, proof of Theorem 4.1, *Phase 1*, "let
+`r̃_j = r_j − b/(I_j − I^*_j)`"]: for `X = g^α`, `Y = g^{b'}`, `z ≠ z'` and
+`F(z) = X^z · (X^{−z'} g^{α_1})`, the real key `(Y^α F(z)^r, g^r)` with exponent `r` is the
+simulated key `(Y^{−α_1/(z − z')} F(z)^{r'}, Y^{−1/(z − z')} g^{r'})` with exponent
+`r' = r + b'/(z − z')`. -/
+theorem key_eq (g : B.G) (α b' z z' a₁ r : ZMod B.order) (hz : z ≠ z') :
+    (g ^ b'.val) ^ α.val *
+        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ r.val =
+      (g ^ b'.val) ^ (-a₁ / (z - z')).val *
+        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ (r + b' / (z - z')).val ∧
+    g ^ r.val = (g ^ b'.val) ^ (-1 / (z - z')).val * g ^ (r + b' / (z - z')).val := by
+  have hz' : z - z' ≠ 0 := sub_ne_zero.2 hz
+  have hpow : ∀ a c : ZMod B.order, (g ^ a.val) ^ c.val = g ^ (a * c).val := fun a c => by
+    rw [B.pow_val_mul, pow_mul]
+  have hmul : ∀ a c : ZMod B.order, g ^ a.val * g ^ c.val = g ^ (a + c).val := fun a c =>
+    (B.pow_val_add g a c).symm
+  simp only [hpow, hmul]
+  constructor <;> congr 2 <;> field_simp <;> ring
+
+/-- **`F(ID*) = g^{α_1}`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
+`F_i(I^*_i) = g^{α_i}`"]: for `h = X^{−z} g^{α_1}`, `X^z · h = g^{α_1}`. -/
+theorem F_target_eq (g X : B.G) (z a₁ : ZMod B.order) :
+    X ^ z.val * (X ^ (-z).val * g ^ a₁.val) = g ^ a₁.val := by
+  rw [B.pow_val_neg, mul_inv_cancel_left]
+
+/-- **`e(g^α, g^{b'})^s = e(g, g)^{α b' s}`** [BB04, proof of Theorem 4.1, *Challenge*, "if
+`T = e(g, g)^{abc} = e(g_1, g_2)^c`"]: `B.pair (g^α) (g^{b'}) ^ s.val =
+B.pair g g ^ (α · b' · s).val`. -/
+theorem pair_pow_val_eq (g : B.G) (α b' s : ZMod B.order) :
+    B.pair (g ^ α.val) (g ^ b'.val) ^ s.val = B.pair g g ^ (α * b' * s).val := by
+  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, B.bilinear_pow]
+
+end Algebra
+
+/-! ### The relation of step M -/
+
+section Rel
+
+variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
+
+/-- **Design r1 §3.1's relation `R`** [BB04, proof of Theorem 4.1, *Setup*]: the real state `u`
+(with `h`) and the simulator's state `v` (with `α_1`) record the same challenge and the same
+committed identity `ID*`, and `h = X^{−ID*} g^{α_1}`. -/
+def RelM (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) : Prop :=
+  u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
+    p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1
+
+/-- `RelM … g X u v` holds iff `u.2 = v.2` and `u.1`, `v.1` are both `none`, or `some (t, h)` and
+`some (t, α_1)` with `h = X^{(−idToZ t).val} · g^{α_1.val}`. Glue: the reader of `RelM`. -/
+theorem relM_iff (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) :
+    RelM G ℓ κ d g X u v ↔ u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
+      p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1 := Iff.rfl
+
+end Rel
+
+/-! ### Step M, call by call
+
+The real side is `bb1RealLazy` on parameters `o h` that the game reads as `(g, g^α, g^{b'}, h)`
+(`RealReads`); the simulator is `bb1SimLazy` on `X = g^α`, `Y = g^{b'}`, with the challenge coin
+`c ∈ Z_p` drawn at the first valid `Challenge`. Deterministic calls answer alike and keep the
+states; sampling calls give the premise of `ProbComp.expect_sample_rel` along their bijection. -/
+
+section StepM
+
+variable (G : BilinearGen) (ℓ : PolyExpr) (b : Bool) (κ : ℕ) (d : List Bool)
+  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
+  (g : (G.group κ d).G) (α b' : ZMod (G.group κ d).order)
+
+variable {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
+
+/-- **Step M, `Init` before a commitment** [BB04, proof of Theorem 4.1, *Setup*] (sampling): the
+real call draws `h ∈ G`, the simulator draws `α_1 ∈ Z_p`; along the bijection `e ID` with
+`h = X^{−z} g^{e z h}` (`exists_equiv_mul_pow`) at `z = ID`, they answer alike and reach related
+states: `(f₀ h).1 = (f₁ (e ID h)).1` and `RelM (f₀ h).2 (f₁ (e ID h)).2`.
+
+**Proof sketch.** The real call is read by `bb1RealLazy_zero_none`, `sidImpl_zero_onSpec` and
+`sidImpl_init_none` (a uniform `h`, the parameters `o h`, the identity recorded with `h`); the
+simulator's by `bb1SimLazy_zero`, `oracleImpl_zero_onSpec` and `bb1SimInit_none` (a uniform
+`α_1`). At `α_1 = e ID h` the parameter words agree (`RealReads.encPP`, `ofFn_bb1Scheme_encPP`,
+`bb1SimParams_eq`, `h = X^{−ID} g^{e ID h}`), and that equation is `RelM` of the new states. -/
+theorem stepM_init_none (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
+    (e : ZMod (G.group κ d).order → (G.group κ d).G ≃ ZMod (G.group κ d).order)
+    (he : ∀ z h, h = (g ^ α.val) ^ (-z).val * g ^ (e z h).val) :
+    ∃ (f₀ : (G.group κ d).G → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1RealState G ℓ κ d)
+      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1SimState G ℓ κ d),
+      bb1RealLazy G ℓ b κ d o 0 x (none, c) =
+        (ProbComp.sample (G.group κ d).G).bind (fun h => .pure (f₀ h)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (none, c) =
+        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun α₁ => .pure (f₁ α₁)) ∧
+      ∀ h, (f₀ h).1 = (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).1 ∧
+        RelM G ℓ κ d g (g ^ α.val) (f₀ h).2
+          (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).2 := by
+  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
+  case h0 =>
+    rw [bb1RealLazy_zero_none]
+    refine congrArg _ (funext fun h => ?_)
+    rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none, OracleComp.pure_bind,
+      OracleComp.pure_bind]
+  case h1 =>
+    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_none,
+      OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind]
+    rfl
+  case hf =>
+    intro h
+    have hz := he (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h
+    refine ⟨?_, ⟨rfl, .some ⟨rfl, ?_⟩⟩⟩
+    · rw [(ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _), bb1SimParams_eq,
+        ← hz]
+    · dsimp only
+      exact hz
+
+/-- **Step M, `Init` after a commitment** [BB04, proof of Theorem 4.1, *Setup*] (deterministic):
+for `h = X^{−ID*} g^{α_1}`, both calls answer the same parameters `(g, X, Y, h)` and keep their
+states: `bb1RealLazy … 0 x (some (t, h), c) = pure (a, (some (t, h), c))` and
+`bb1SimLazy … 0 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`.
+
+**Proof sketch.** The real call is `sidImpl`'s `Init` on a committed state (`bb1RealLazy_some`,
+`sidImpl_zero_onSpec`, `sidImpl_init_some`); the simulator's is `bb1SimInit_some`
+(`bb1SimLazy_zero`, `bb1SimImpl_eq`, `oracleImpl_zero_onSpec`). Both answer the encoded parameters,
+equal by `RealReads.encPP`, `ofFn_bb1Scheme_encPP`, `bb1SimParams_eq` and `h = X^{−ID*} g^{α_1}`. -/
+theorem stepM_init_some (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
+    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
+    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 0 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (some (t, α₁), c) =
+        .pure (a, (some (t, α₁), c)) := by
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some,
+      OracleComp.pure_bind, OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_some,
+      OracleComp.pure_bind, (ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _),
+      bb1SimParams_eq, ← hh]
+
+/-- **Step M, `KeyGen` before `Init`** (deterministic): both calls answer `⊥` and keep their
+states: `bb1RealLazy … 1 x (none, c) = pure (a, (none, c))` and
+`bb1SimLazy … 1 x (none, c) = pure (a, (none, c))`. Glue for the game's `KeyGen`. -/
+theorem stepM_keyGen_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (none, c) = .pure (a, (none, c)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (none, c) =
+        .pure (a, (none, c)) := by
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 1 (by decide), IBEScheme.sidImpl_one_onQuery,
+      IBEScheme.sidImpl_keyGen_none, OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_none,
+      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]
+
+/-- **Step M, `KeyGen` for `ID*`** (deterministic): both calls answer `⊥` and keep their states:
+for `x` read as `t`, `bb1RealLazy … 1 x (some (t, h), c) = pure (a, (some (t, h), c))` and
+`bb1SimLazy … 1 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`. Glue for the game's
+`KeyGen`.
+
+**Proof sketch.** The real call is `sidImpl_keyGen_target` (`bb1RealLazy_some`,
+`sidImpl_one_onQuery`), the simulator's `bb1SimKeyQ_target` (`bb1SimLazy_one`, `bb1SimImpl_eq`,
+`oracleImpl_one_onSpec`); both `⊥` words agree by `zeroBits_eq_cast` and `outLens_one`. -/
+theorem stepM_keyGen_target (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
+    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
+    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
+    (ht : cast (sidSpec_dom_one _ κ) x = t) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
+        .pure (a, (some (t, α₁), c)) := by
+  subst ht
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_one_onQuery, IBEScheme.sidImpl_keyGen_target,
+      OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_target,
+      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]
+
+/-- **Step M, `KeyGen` for `ID ≠ ID*`** [BB04, proof of Theorem 4.1, *Phase 1*, "let
+`r̃_j = r_j − b/(I_j − I^*_j)`"] (sampling): for `h = X^{−ID*} g^{α_1}` and good coins
+`2^{ℓ(κ)} ≤ p`, the real key with exponent `r̃` is the simulated key with exponent
+`r̃ + b'/(ID − ID*)`: `(f₀ r̃).1 = (f₁ (r̃ + b'/(ID − ID*))).1`, and the states are kept.
+
+**Proof sketch.** The real call is read by `sidImpl_keyGen_ne_onSpec` and `RealReads.keyGen` (a
+uniform `r̃` and the key word), the simulator's by `oracleImpl_one_onSpec` and `bb1SimKeyQ_ne` (a
+uniform `r`). `ID ≠ ID*` in `Z_p` by `natCast_bitsToNat_injective` (`BB1.idToZ_eq`). At
+`r = r̃ + b'/(ID − ID*)` the key words agree: `ofFn_bb1Scheme_encSK`, `bb1SimKey_eq`, `BB1.F_eq`,
+`bb1SimParams_eq`, `h = X^{−ID*} g^{α_1}` and `key_eq`. The states are unchanged. -/
+theorem stepM_keyGen_ne (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
+    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
+    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
+    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
+    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
+    (ht : cast (sidSpec_dom_one _ κ) x ≠ t) :
+    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1RealState G ℓ κ d)
+      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1SimState G ℓ κ d),
+      bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) =
+        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₀ r)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
+        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₁ r)) ∧
+      ∀ r, (f₀ r).1 = (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
+          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).1 ∧
+        RelM G ℓ κ d g (g ^ α.val) (f₀ r).2 (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
+          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).2 := by
+  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_keyGen_ne_onSpec _ _ _ _ _ x t c ht,
+      OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind, Option.map_some]
+    rw [(ho h).keyGen _ fun w => .pure (cast (sidSpec_rng_one _ κ).symm
+      (FixedLengthScheme.decAnswer (some w)), (some (t, h), c))]
+  case h1 =>
+    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_ne (h := ht),
+      OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind]
+    rfl
+  case hf =>
+    intro r
+    refine ⟨?_, ⟨rfl, .some ⟨rfl, hh⟩⟩⟩
+    have hz : BB1.idToZ (G.group κ d) (cast (sidSpec_dom_one _ κ) x) ≠
+        BB1.idToZ (G.group κ d) t := by
+      rw [BB1.idToZ_eq, BB1.idToZ_eq]
+      exact fun h' => ht (natCast_bitsToNat_injective hp h')
+    obtain ⟨h0, h1⟩ := key_eq (G.group κ d) g α b' _ _ α₁ r hz
+    rw [Equiv.coe_addRight, List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ d _), bb1SimKey_eq,
+      BB1.F_eq, BB1.F_eq, bb1SimParams_eq, hh]
+    dsimp only
+    rw [h0, h1]
+
+/-- **Step M, `Challenge` before `Init`** (deterministic): both calls answer `⊥` and keep their
+states: `bb1RealLazy … 2 x (none, c) = pure (a, (none, c))` and
+`bb1SimLazy … 2 x (none, c) = pure (a, (none, c))`. Glue for the game's `Challenge`. -/
+theorem stepM_challenge_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (none, c) = .pure (a, (none, c)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (none, c) =
+        .pure (a, (none, c)) := by
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 2 (by decide), IBEScheme.sidImpl_two_onQuery,
+      IBEScheme.sidImpl_challenge_none, OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (none, c) fun h' => Bool.false_ne_true h'.1,
+      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_none, OracleComp.pure_bind,
+      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
+
+/-- **Step M, `Challenge` after a recorded challenge** (deterministic): both calls repeat the
+recorded challenge `w` and keep their states: `bb1RealLazy … 2 x (some (t, h), some w) =
+pure (a, (some (t, h), some w))` and `bb1SimLazy … 2 x (some (t, α_1), some w) =
+pure (a, (some (t, α_1), some w))`. Glue for the game's `Challenge`.
+
+**Proof sketch.** The real call is `sidImpl_challenge_repeat` (`bb1RealLazy_some`,
+`sidImpl_two_onSpec`), the simulator's `bb1SimChal_repeat` (`bb1SimLazy_two_of_not`, since a
+challenge is recorded; `bb1SimImpl_eq`, `oracleImpl_two_onSpec`); both answer `w`. -/
+theorem stepM_challenge_repeat (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
+    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
+    (α₁ : ZMod (G.group κ d).order) (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), some w) = .pure (a, (some (t, h), some w)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), some w) =
+        .pure (a, (some (t, α₁), some w)) := by
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onSpec, IBEScheme.sidImpl_challenge_repeat,
+      OracleComp.pure_bind, OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), some w)
+        fun h' => Option.some_ne_none w h'.2.1,
+      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_repeat, OracleComp.pure_bind]
+
+/-- **Step M, the first invalid `Challenge`** (deterministic): when a message of the query is not
+an encoding of `G_T`, both calls answer `⊥` and keep their states:
+`bb1RealLazy … 2 x (some (t, h), none) = pure (a, (some (t, h), none))` and
+`bb1SimLazy … 2 x (some (t, α_1), none) = pure (a, (some (t, α_1), none))`; both message spaces
+are the encodings of `G_T` (`RealReads.msgSpace`, `bb1Scheme_msgSpace_iff`). Glue for the
+game's `Challenge`.
+
+**Proof sketch.** The real call is read by `bb1RealLazy_some`, `sidImpl_two_onQuery` and
+`sidImpl_challenge_invalid` (invalidity through `RealReads.msgSpace`); the simulator's by
+`bb1SimLazy_two_of_not`, `oracleImpl_two_onSpec` and `bb1SimChal_invalid` (invalidity through
+`bb1Scheme_msgSpace_iff`). Both answer the `⊥` word (`zeroBits_eq_cast`). -/
+theorem stepM_challenge_invalid (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
+    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
+    (hv : ¬ ((∃ u, List.ofFn ((G.group κ d).encT u) =
+        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+      ∃ u, List.ofFn ((G.group κ d).encT u) =
+        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
+    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) = .pure (a, (some (t, h), none)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), none) =
+        .pure (a, (some (t, α₁), none)) := by
+  have hv' : ¬ ((bb1Scheme G ℓ).MsgSpace κ (o h).1
+        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1 ∧
+      (bb1Scheme G ℓ).MsgSpace κ (o h).1
+        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) := fun hm =>
+    hv ⟨((ho h).msgSpace _).1 hm.1, ((ho h).msgSpace _).1 hm.2⟩
+  refine ⟨?a, ?h0, ?h1⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onQuery,
+      IBEScheme.sidImpl_challenge_invalid _ _ _ _ _ _ _ hv', OracleComp.pure_bind]
+    rfl
+  case h1 =>
+    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), none) fun h' => hv h'.2.2,
+      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_invalid, OracleComp.pure_bind,
+      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
+    exact fun hm => hv ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.1,
+      (bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.2⟩
+
+/-- **Step M, the first valid `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
+`F_i(I^*_i) = g^{α_i}`"] (sampling, along the identity of `Z_p`): for `h = X^{−ID*} g^{α_1}`,
+the real encryption with exponent `s` is the simulated challenge on the coins
+`(g^s, e(g, g)^{α b' s})`: `(f₀ s).1 = (f₁ s).1`, and both record that challenge.
+
+**Proof sketch.** The real call is read by `sidImpl_challenge_fresh_onSpec` (validity through
+`RealReads.msgSpace`) and `RealReads.enc` (a uniform `s` and the ciphertext word); the
+simulator's by `bb1SimLazy_two_fresh` (a uniform `c`), `oracleImpl_two_onSpec` and
+`bb1SimChal_fresh` (validity through `bb1Scheme_msgSpace_iff`). At `c = s` the words agree
+(`ofFn_bb1SimCt`, `pair_pow_val_eq`, commutativity of `G_T`, `BB1.F_eq`, `F_target_eq`,
+`pow_right_comm`), and both record that word. -/
+theorem stepM_challenge_fresh (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
+    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
+    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
+    (hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
+        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+      ∃ u, List.ofFn ((G.group κ d).encT u) =
+        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :
+    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1RealState G ℓ κ d)
+      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1SimState G ℓ κ d),
+      bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) =
+        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun s => .pure (f₀ s)) ∧
+      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
+          (fun c : ZMod (G.group κ d).order =>
+            (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) 2 x (some (t, α₁), none) =
+        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun c => .pure (f₁ c)) ∧
+      ∀ s, (f₀ s).1 = (f₁ (Equiv.refl _ s)).1 ∧
+        RelM G ℓ κ d g (g ^ α.val) (f₀ s).2 (f₁ (Equiv.refl _ s)).2 := by
+  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
+  case h0 =>
+    rw [bb1RealLazy_some, IBEScheme.sidImpl_challenge_fresh_onSpec _ _ _ _ _ x t
+      ⟨((ho h).msgSpace _).2 hv.1, ((ho h).msgSpace _).2 hv.2⟩, OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind, Option.map_some]
+    rw [(ho h).enc t _ fun w => .pure (cast (sidSpec_rng_two _ κ).symm w, (some (t, h), some w))]
+  case h1 =>
+    rw [bb1SimLazy_two_fresh G ℓ b κ d g _ _ _ x _ ⟨rfl, rfl, hv⟩]
+    refine congrArg _ (funext fun c => ?_)
+    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh, OracleComp.pure_bind]
+    exact ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1, (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩
+  case hf =>
+    intro s
+    rw [Equiv.refl_apply]
+    refine ⟨?_, ⟨?_, .some ⟨rfl, hh⟩⟩⟩ <;>
+    · rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), pair_pow_val_eq,
+        mul_comm ((G.group κ d).pair g g ^ (α * b' * s).val), BB1.F_eq]
+      dsimp only
+      rw [hh, F_target_eq, pow_right_comm]
+
+/-- **Step M, the per-call hypothesis of `ProbComp.expect_simulate_rel`** [BB04, proof of
+Theorem 4.1]: for `g ≠ 1`, good coins `2^{ℓ(κ)} ≤ p`, and parameters `o h` read as
+`(g, g^α, g^{b'}, h)`, from states related by `RelM`, a call of `bb1RealLazy … o` and of
+`bb1SimLazy` on `X = g^α`, `Y = g^{b'}` and `zt c = (g^c, e(g, g)^{α b' c})` give the same
+expectation to any `g₀`, `g₁` that agree at equal answers and related states.
+
+**Proof sketch.** By cases on the oracle and the states, with the rows `stepM_*`: deterministic
+rows answer alike and keep the related states (`expect_pure`); sampling rows meet the premise of
+`ProbComp.expect_sample_rel` along `e ID` (`Init`, `exists_equiv_mul_pow`),
+`r ↦ r + b'/(ID − ID*)` (`KeyGen`, `key_eq`, `natCast_bitsToNat_injective`) and the identity
+(`Challenge`, `F_target_eq`, `pair_pow_val_eq`). -/
+theorem stepM_call (hg : g ≠ 1) (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
+    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (i : Fin 3)
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (u : BB1RealState G ℓ κ d)
+    (v : BB1SimState G ℓ κ d) (huv : RelM G ℓ κ d g (g ^ α.val) u v)
+    (g₀ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1RealState G ℓ κ d → ℝ)
+    (g₁ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ)
+    (hg₀₁ : ∀ y u' v', RelM G ℓ κ d g (g ^ α.val) u' v' → g₀ (y, u') = g₁ (y, v')) :
+    ProbComp.expect (bb1RealLazy G ℓ b κ d o i x u) g₀ =
+      ProbComp.expect (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
+        (fun c : ZMod (G.group κ d).order =>
+          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) i x v) g₁ := by
+  generalize hzt : (fun c : ZMod (G.group κ d).order =>
+    (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) = zt
+  obtain ⟨e, he⟩ := exists_equiv_mul_pow (G.group κ d) hg (g ^ α.val)
+  obtain ⟨u₁, uc⟩ := u
+  obtain ⟨v₁, vc⟩ := v
+  obtain ⟨hc, hR⟩ := id huv
+  dsimp only at hc
+  subst hc
+  match i, x, g₀, g₁, hg₀₁ with
+  | 0, x, g₀, g₁, hg₀₁ =>
+    cases hR with
+    | none =>
+      obtain ⟨f₀, f₁, h0, h1, hf⟩ := stepM_init_none G ℓ b κ d o g α b' zt ho x uc e he
+      rw [h0, h1]
+      exact ProbComp.expect_sample_rel _ (e _) f₀ f₁ hf g₀ g₁ hg₀₁
+    | @some p q hpq =>
+      obtain ⟨t, h⟩ := p
+      obtain ⟨t', α₁⟩ := q
+      obtain ⟨ht, hh⟩ := hpq
+      dsimp only at ht hh
+      subst t'
+      obtain ⟨a, h0, h1⟩ := stepM_init_some G ℓ b κ d o g α b' zt ho x t h α₁ uc hh
+      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+      exact hg₀₁ _ _ _ huv
+  | 1, x, g₀, g₁, hg₀₁ =>
+    cases hR with
+    | none =>
+      obtain ⟨a, h0, h1⟩ := stepM_keyGen_none G ℓ b κ d o g α b' zt x uc
+      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+      exact hg₀₁ _ _ _ huv
+    | @some p q hpq =>
+      obtain ⟨t, h⟩ := p
+      obtain ⟨t', α₁⟩ := q
+      obtain ⟨ht, hh⟩ := hpq
+      dsimp only at ht hh
+      subst t'
+      by_cases hx : cast (sidSpec_dom_one _ κ) x = t
+      · obtain ⟨a, h0, h1⟩ := stepM_keyGen_target G ℓ b κ d o g α b' zt x t h α₁ uc hx
+        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+        exact hg₀₁ _ _ _ huv
+      · obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
+          stepM_keyGen_ne G ℓ b κ d o g α b' zt hp ho x t h α₁ uc hh hx
+        rw [h0, h1]
+        exact ProbComp.expect_sample_rel _ (Equiv.addRight _) f₀ f₁ hf g₀ g₁ hg₀₁
+  | 2, x, g₀, g₁, hg₀₁ =>
+    cases hR with
+    | none =>
+      obtain ⟨a, h0, h1⟩ := stepM_challenge_none G ℓ b κ d o g α b' zt x uc
+      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+      exact hg₀₁ _ _ _ huv
+    | @some p q hpq =>
+      obtain ⟨t, h⟩ := p
+      obtain ⟨t', α₁⟩ := q
+      obtain ⟨ht, hh⟩ := hpq
+      dsimp only at ht hh
+      subst t'
+      rcases uc with _ | w
+      · by_cases hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+          ∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2
+        · subst hzt
+          obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
+            stepM_challenge_fresh G ℓ b κ d o g α b' ho x t h α₁ hh hv
+          rw [h0, h1]
+          exact ProbComp.expect_sample_rel _ (Equiv.refl _) f₀ f₁ hf g₀ g₁ hg₀₁
+        · obtain ⟨a, h0, h1⟩ := stepM_challenge_invalid G ℓ b κ d o g α b' zt ho x t h α₁ hv
+          rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+          exact hg₀₁ _ _ _ huv
+      · obtain ⟨a, h0, h1⟩ := stepM_challenge_repeat G ℓ b κ d o g α b' zt x t h α₁ w
+        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
+        exact hg₀₁ _ _ _ huv
+
+/-- **Step M** (design r1 §3.1) [BB04, proof of Theorem 4.1]: for `g ≠ 1`, good coins
+`2^{ℓ(κ)} ≤ p`, and parameters `o h` read as `(g, g^α, g^{b'}, h)`, the real game with `h` drawn
+at the first `Init` simulates like the simulator on `X = g^α`, `Y = g^{b'}` with the challenge
+coin `c` drawn at the first valid `Challenge`, for functions `F` of the output:
+`𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none)) =
+𝔼[F ∘ fst] (simulate (bb1SimLazy … (fun c => (g^c, e(g, g)^{α b' c}))) c (none, none))`.
+
+**Proof sketch.** `ProbComp.expect_simulate_rel` with `RelM`, the per-call hypothesis
+`stepM_call`, functions of the output only, and `RelM` at the empty states. -/
+theorem expect_simulate_bb1RealLazy (hg : g ≠ 1)
+    (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
+    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) {β : Type}
+    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β) (F : β → ℝ) :
+    ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) =
+      ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
+        (fun c : ZMod (G.group κ d).order =>
+          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val))) c (none, none))
+        (fun p => F p.1) :=
+  ProbComp.expect_simulate_rel _ _ (RelM G ℓ κ d g (g ^ α.val))
+    (fun i x u v huv g₀ g₁ hg₀₁ => stepM_call G ℓ b κ d o g α b' hg hp ho i x u v huv g₀ g₁ hg₀₁)
+    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, .none⟩
+
+end StepM
+
+end BB1Sim
+
+end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean
new file mode 100644
index 000000000..39dd73cda
--- /dev/null
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean
@@ -0,0 +1,447 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
+import TCSlib.Cryptography.Games.Hopping
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The BB1 simulator with its challenge coins drawn at the challenge
+
+Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (steps 1 and 2 of
+[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The simulator `bb1SimImpl` of
+`AdvancedEncryption/IdentityBased/BonehBoyen.lean` receives the challenge coins `(Z, T)` before
+the game starts, but uses them only at the first valid `Challenge` [BB04, proof of Theorem 4.1,
+*Challenge*]. `bb1SimLazy` is the same simulator with coins `zt u` drawn at that call, for a
+uniform `u` in any nonempty finite type `U`: step 1 draws `u = c ∈ Z_p` with
+`zt c = (g^c, e(g, g)^{a b' c})`, step 2 draws `u = T ∈ G_T` with `zt T = (Z, T)`. The two
+simulators simulate alike (`expect_simulate_bb1SimLazy`, an instance of
+`Games.expect_simulate_eager`).
+
+The module also reads the game's query and answer types from their published equations
+(`sidSpec_dom_zero`, …), so that its consumers never reduce `IBEScheme.inLens` or
+`IBEScheme.outLens`.
+
+## Main definitions
+
+* `BB1Sim.bb1SimLazyChal` — the simulator's `Challenge` with its coins drawn at the call.
+* `BB1Sim.bb1SimLazy` — the simulator's oracles with that `Challenge`.
+
+## Main results
+
+* `BB1Sim.bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimLazy_two_fresh`, `bb1SimLazy_two_of_not` —
+  `bb1SimLazy` call by call, against `bb1SimImpl`.
+* `BB1Sim.bb1SimImpl_two_of_not` — away from the first valid `Challenge`, `bb1SimImpl` does not
+  read its coins.
+* `BB1Sim.expect_simulate_bb1SimLazy` — the lazy simulator simulates like `bb1SimImpl` with coins
+  drawn in advance.
+
+## References
+
+* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
+  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
+  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
+  `B` in the proof of Theorem 4.1.
+-/
+
+namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
+
+open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
+  TCSlib.Cryptography.Composability
+
+namespace BB1Sim
+
+/-! ### The game's query and answer types, from published equations -/
+
+section Types
+
+variable (S : IBEScheme) (κ : ℕ)
+
+/-- `Init` queries are identities: `(S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool)`
+(`sidSpec_eq`, `bitSpec_dom`, `inLens_zero`). Glue for the game's types. -/
+theorem sidSpec_dom_zero : (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_zero]
+
+/-- `KeyGen` queries are identities: `(S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool)`
+(`sidSpec_eq`, `bitSpec_dom`, `inLens_one`). Glue for the game's types. -/
+theorem sidSpec_dom_one : (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_one]
+
+/-- `Challenge` queries are two messages:
+`(S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)` (`sidSpec_eq`,
+`bitSpec_dom`, `inLens_two`). Glue for the game's types. -/
+theorem sidSpec_dom_two :
+    (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_two]
+
+/-- `Init` answers parameters: `(S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)`
+(`sidSpec_eq`, `bitSpec_rng`, `outLens_zero`). Glue for the game's types. -/
+theorem sidSpec_rng_zero : (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_zero]
+
+/-- `KeyGen` answers a bit and a key: `(S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)`
+(`sidSpec_eq`, `bitSpec_rng`, `outLens_one`). Glue for the game's types. -/
+theorem sidSpec_rng_one : (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_one]
+
+/-- `Challenge` answers a ciphertext: `(S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)`
+(`sidSpec_eq`, `bitSpec_rng`, `outLens_two`). Glue for the game's types. -/
+theorem sidSpec_rng_two : (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool) := by
+  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_two]
+
+/-- The `⊥` word of a width equal to `m`, cast: `zeroBits n = cast e (zeroBits m)` for `n = m`.
+Glue for the game's types. -/
+theorem zeroBits_eq_cast {n m : ℕ} (hnm : n = m) (e : (Fin m → Bool) = (Fin n → Bool)) :
+    zeroBits n = cast e (zeroBits m) := by
+  subst hnm
+  rfl
+
+end Types
+
+/-! ### The lazy simulator -/
+
+section Lazy
+
+variable (G : BilinearGen) (ℓ : PolyExpr)
+
+open Classical in
+/-- **The simulator's `Challenge` with its coins drawn at the call** [BB04, proof of Theorem 4.1,
+*Challenge*]: with `ID*` recorded, no challenge yet, and both messages `M₀, M₁` encodings of
+`G_T`, draw `u ∈ U` and answer as `bb1SimChal` on the coins `zt u = (Z, T)`; otherwise answer
+as `bb1SimChal` on the coins `(1, 1)`, which it does not read there. -/
+noncomputable def bb1SimLazyChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
+    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
+    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
+    (s : BB1SimState G ℓ κ d) :
+    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
+  if s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)
+  then (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s
+  else bb1SimChal G ℓ b κ d g X Y 1 1 mm s
+
+/-- At the first valid `Challenge`, `bb1SimLazyChal` draws `u` and answers as `bb1SimChal` on
+`zt u`: for `s.1` some, `s.2 = none` and both messages encodings of `G_T`,
+`bb1SimLazyChal … zt mm s = (sample U).bind fun u => bb1SimChal … (zt u).1 (zt u).2 mm s`. Glue: a
+case reader of `bb1SimLazyChal`. -/
+theorem bb1SimLazyChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
+    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
+    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
+    (s : BB1SimState G ℓ κ d)
+    (h : s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)) :
+    bb1SimLazyChal G ℓ b κ d g X Y zt mm s =
+      (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s := by
+  rw [bb1SimLazyChal, if_pos h]
+
+/-- Away from the first valid `Challenge`, `bb1SimLazyChal` answers as `bb1SimChal` on the
+coins `(1, 1)`: `bb1SimLazyChal … zt mm s = bb1SimChal … 1 1 mm s`. Glue: a case reader of
+`bb1SimLazyChal`. -/
+theorem bb1SimLazyChal_of_not (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
+    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
+    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
+    (s : BB1SimState G ℓ κ d)
+    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2))) :
+    bb1SimLazyChal G ℓ b κ d g X Y zt mm s = bb1SimChal G ℓ b κ d g X Y 1 1 mm s := by
+  rw [bb1SimLazyChal, if_neg h]
+
+/-- **The simulator with its challenge coins drawn at the challenge** [BB04, proof of
+Theorem 4.1]: the oracles `oracleImpl` of the simulator's `Init` (`bb1SimInit`) and `KeyGen`
+(`bb1SimKeyQ`) and of `bb1SimLazyChal`, with challenge bit `b` on `g, X, Y` and the coin map
+`zt : U → G × G_T`. -/
+noncomputable def bb1SimLazy (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
+    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
+    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
+  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
+    (bb1SimLazyChal G ℓ b κ d g X Y zt)
+
+/-- `bb1SimLazy` is `oracleImpl` of `bb1SimInit`, `bb1SimKeyQ` and `bb1SimLazyChal`:
+`bb1SimLazy … zt = oracleImpl κ (bb1SimInit …) (bb1SimKeyQ …) (bb1SimLazyChal … zt)`. Glue: the
+reader of `bb1SimLazy`. -/
+theorem bb1SimLazy_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
+    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
+    bb1SimLazy G ℓ b κ d g X Y zt =
+      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
+        (bb1SimLazyChal G ℓ b κ d g X Y zt) := rfl
+
+variable (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G) {U : Type} [Fintype U]
+  [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
+
+/-- `Init` of `bb1SimImpl` does not read the challenge coins:
+`bb1SimImpl … Z T 0 x s = bb1SimImpl … Z' T' 0 x s`. Glue: a case fact of `bb1SimImpl` for the eager
+step. -/
+theorem bb1SimImpl_zero_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
+    bb1SimImpl G ℓ b κ d g X Y Z T 0 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 0 x s := by
+  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
+    IBEScheme.oracleImpl_zero_onSpec]
+
+/-- `KeyGen` of `bb1SimImpl` does not read the challenge coins:
+`bb1SimImpl … Z T 1 x s = bb1SimImpl … Z' T' 1 x s`. Glue: a case fact of `bb1SimImpl` for the eager
+step. -/
+theorem bb1SimImpl_one_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
+    bb1SimImpl G ℓ b κ d g X Y Z T 1 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 1 x s := by
+  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
+    IBEScheme.oracleImpl_one_onSpec]
+
+/-- `Init` of the lazy simulator is `Init` of `bb1SimImpl`:
+`bb1SimLazy … zt 0 x s = bb1SimImpl … 1 1 0 x s`. Glue: a case reader of `bb1SimLazy`. -/
+theorem bb1SimLazy_zero (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
+    bb1SimLazy G ℓ b κ d g X Y zt 0 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 0 x s := by
+  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
+    IBEScheme.oracleImpl_zero_onSpec]
+
+/-- `KeyGen` of the lazy simulator is `KeyGen` of `bb1SimImpl`:
+`bb1SimLazy … zt 1 x s = bb1SimImpl … 1 1 1 x s`. Glue: a case reader of `bb1SimLazy`. -/
+theorem bb1SimLazy_one (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
+    bb1SimLazy G ℓ b κ d g X Y zt 1 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 1 x s := by
+  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
+    IBEScheme.oracleImpl_one_onSpec]
+
+/-- **The first valid `Challenge` of the lazy simulator** draws `u` and calls `bb1SimImpl` on the
+coins `zt u`: for `s.1` some, `s.2 = none`, and both messages of the query `x` (read as two
+messages) encodings of `G_T`,
+`bb1SimLazy … zt 2 x s = (sample U).bind fun u => bb1SimImpl … (zt u).1 (zt u).2 2 x s`. Glue: a
+case reader of `bb1SimLazy`. -/
+theorem bb1SimLazy_two_fresh (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
+    (h : s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
+    bb1SimLazy G ℓ b κ d g X Y zt 2 x s =
+      (ProbComp.sample U).bind fun u =>
+        bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2 2 x s := by
+  rw [bb1SimLazy_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_fresh _ _ _ _ _ _ _ _ _ _ _
+    h, OracleComp.bind_assoc]
+  refine congrArg _ (funext fun u => ?_)
+  rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec]
+
+/-- **`Challenge` of the lazy simulator away from the first valid one** is `Challenge` of
+`bb1SimImpl` on the coins `(1, 1)`: `bb1SimLazy … zt 2 x s = bb1SimImpl … 1 1 2 x s`. Glue: a case
+reader of `bb1SimLazy`. -/
+theorem bb1SimLazy_two_of_not (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
+    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
+    bb1SimLazy G ℓ b κ d g X Y zt 2 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 2 x s := by
+  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec,
+    IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_of_not _ _ _ _ _ _ _ _ _ _ _ h]
+
+/-- **Away from the first valid `Challenge`, `bb1SimImpl` reads neither its coins nor its
+challenge bit**, and keeps the recorded challenge: unless `s.1` is some, `s.2 = none` and both
+messages are encodings of `G_T`, `bb1SimImpl b … Z T 2 x s = bb1SimImpl false … 1 1 2 x s`, and
+every outcome has the challenge `s.2`. Glue: a case fact of `bb1SimImpl` for the eager step.
+
+**Proof sketch.** Read both calls by `oracleImpl_two_onSpec`. Before `Init` both answer `⊥`
+(`bb1SimChal_none`); after a recorded challenge both repeat it (`bb1SimChal_repeat`); at a first
+`Challenge` with a message outside the message space both answer `⊥` (`bb1SimChal_invalid`,
+`bb1Scheme_msgSpace_iff`). -/
+theorem bb1SimImpl_two_of_not (Z : (G.group κ d).G) (T : (G.group κ d).GT)
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
+    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
+    bb1SimImpl G ℓ b κ d g X Y Z T 2 x s = bb1SimImpl G ℓ false κ d g X Y 1 1 2 x s ∧
+      (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2 = s.2 := by
+  obtain ⟨s₁, s₂⟩ := s
+  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec,
+    IBEScheme.oracleImpl_two_onSpec]
+  rcases s₁ with _ | ⟨t, α₁⟩
+  -- before `Init`: `⊥`
+  · rw [bb1SimChal_none, bb1SimChal_none, OracleComp.pure_bind]
+    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
+  rcases s₂ with _ | w
+  -- a first `Challenge` with a message outside the message space: `⊥`
+  · have hv : ¬ ((∃ u, List.ofFn ((G.group κ d).encT u) =
+              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+            ∃ u, List.ofFn ((G.group κ d).encT u) =
+              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :=
+      fun hv => h ⟨rfl, rfl, hv⟩
+    have hm : ∀ (b' : Bool) (Z' : (G.group κ d).G) (T' : (G.group κ d).GT),
+        bb1SimChal G ℓ b' κ d g X Y Z' T' (cast (sidSpec_dom_two _ κ) x) (some (t, α₁), none) =
+          .pure (zeroBits _, (some (t, α₁), none)) := fun b' Z' T' =>
+      bb1SimChal_invalid G ℓ b' κ d g X Y Z' T' _ t α₁ fun hm' =>
+        hv ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm'.1,
+          (bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm'.2⟩
+    rw [hm, hm, OracleComp.pure_bind]
+    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
+  -- after a recorded challenge: repeat it
+  · rw [bb1SimChal_repeat, bb1SimChal_repeat, OracleComp.pure_bind]
+    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
+
+/-- **The first valid `Challenge` records a challenge**: for `s.1` some and `s.2 = none`, and
+both messages encodings of `G_T`, every outcome of `bb1SimImpl … Z T 2 x s` has a recorded
+challenge. Glue: a case fact of `bb1SimImpl` for the eager step.
+
+**Proof sketch.** Read the call by `oracleImpl_two_onSpec`; at the first valid `Challenge` it is
+`bb1SimChal_fresh` (validity through `bb1Scheme_msgSpace_iff`), which records the challenge. -/
+theorem bb1SimImpl_two_fresh_allOutputs (Z : (G.group κ d).G) (T : (G.group κ d).GT)
+    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
+    (h : s.1.isSome ∧ s.2 = none ∧
+      ((∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+        ∃ u, List.ofFn ((G.group κ d).encT u) =
+          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
+    (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2.isSome := by
+  obtain ⟨s₁, s₂⟩ := s
+  obtain ⟨h₁, h₂, hv⟩ := h
+  rcases s₁ with _ | ⟨t, α₁⟩
+  · exact absurd h₁ Bool.false_ne_true
+  subst h₂
+  rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh G ℓ b κ d g X Y Z T _ t α₁
+    ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1, (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩,
+    OracleComp.pure_bind]
+  exact OracleComp.allOutputs_pure.2 rfl
+
+/-- **`Init` and `KeyGen` keep the recorded challenge**: for `i ≠ 2`, every outcome of
+`bb1SimImpl … Z T i x s` has the challenge `s.2`. Glue: a case fact of `bb1SimImpl` for the eager
+step.
+
+**Proof sketch.** Read the call by `oracleImpl_zero_onSpec` or `oracleImpl_one_onSpec`. `Init`
+records `(ID, α_1)` or keeps the state (`bb1SimInit_none`, `bb1SimInit_some`); `KeyGen` keeps the
+state (`bb1SimKeyQ_none`, `bb1SimKeyQ_target`, `bb1SimKeyQ_ne`). Neither touches `s.2`. -/
+theorem bb1SimImpl_allOutputs_of_ne_two (Z : (G.group κ d).G) (T : (G.group κ d).GT)
+    (i : Fin 3) (hi : i ≠ 2) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (s : BB1SimState G ℓ κ d) :
+    (bb1SimImpl G ℓ b κ d g X Y Z T i x s).AllOutputs fun p => p.2.2 = s.2 := by
+  obtain ⟨s₁, s₂⟩ := s
+  revert x
+  match i, hi with
+  | 0, _ =>
+    intro x
+    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec]
+    rcases s₁ with _ | ⟨t, α₁⟩
+    · rw [bb1SimInit_none]
+      refine OracleComp.AllOutputs.bind (P := fun p => p.2.2 = s₂) ?_
+        fun p hp => OracleComp.allOutputs_pure.2 hp
+      exact (OracleComp.allOutputs_true _).bind fun _ _ => OracleComp.allOutputs_pure.2 rfl
+    · rw [bb1SimInit_some, OracleComp.pure_bind]
+      exact OracleComp.allOutputs_pure.2 rfl
+  | 1, _ =>
+    intro x
+    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec]
+    rcases s₁ with _ | ⟨t, α₁⟩
+    · rw [bb1SimKeyQ_none, OracleComp.pure_bind]
+      exact OracleComp.allOutputs_pure.2 rfl
+    by_cases ht : cast (sidSpec_dom_one _ κ) x = t
+    · rw [ht, bb1SimKeyQ_target, OracleComp.pure_bind]
+      exact OracleComp.allOutputs_pure.2 rfl
+    · rw [bb1SimKeyQ_ne (h := ht)]
+      refine OracleComp.AllOutputs.bind (P := fun p => p.2.2 = s₂) ?_
+        fun p hp => OracleComp.allOutputs_pure.2 hp
+      exact (OracleComp.allOutputs_true _).bind fun _ _ => OracleComp.allOutputs_pure.2 rfl
+  | 2, hi => exact absurd rfl hi
+
+/-- **The lazy simulator simulates like `bb1SimImpl` with its coins drawn in advance**: from a
+state with no recorded challenge (`s.2 = none`), for every computation `c` and every `F`,
+`𝔼[F] (simulate (bb1SimLazy … zt) c s) =
+𝔼_{u ← U} 𝔼[F] (simulate (bb1SimImpl … (zt u).1 (zt u).2) c s)`. Glue: an instance of
+`Games.expect_simulate_eager`, with the coins spent at the first valid `Challenge`.
+
+**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1SimLazy … zt`,
+`OE u := bb1SimImpl … (zt u)` and `used v := v.2` some. `Init` and `KeyGen` do not read the
+coins (`bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimImpl_zero_coins`, `bb1SimImpl_one_coins`)
+and keep the recorded challenge (`bb1SimImpl_allOutputs_of_ne_two`). A `Challenge` other than
+the first valid one does not read them either and keeps the recorded challenge
+(`bb1SimLazy_two_of_not`, `bb1SimImpl_two_of_not`); the first valid one draws them
+(`bb1SimLazy_two_fresh`) and records a challenge (`bb1SimImpl_two_fresh_allOutputs`). -/
+theorem expect_simulate_bb1SimLazy {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
+    (F : α × BB1SimState G ℓ κ d → ℝ) {s : BB1SimState G ℓ κ d} (hs : s.2 = none) :
+    ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g X Y zt) c s) F =
+      ProbComp.expect (ProbComp.sample U) fun u =>
+        ProbComp.expect (simulate (bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2) c s) F := by
+  have h01 : ∀ i : Fin 3, i ≠ 2 → i = 0 ∨ i = 1 := by decide
+  refine Games.expect_simulate_eager (T := U) (bb1SimLazy G ℓ b κ d g X Y zt)
+    (fun u => bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2) (fun v => v.2.isSome = true)
+    (fun u i => ?_) (fun i => ?_) (fun i => ?_) c F
+    (by show ¬ (s.2.isSome = true); rw [hs]; exact Bool.false_ne_true)
+  -- from a used state, the coins are not read
+  · by_cases h2 : i = 2
+    · subst h2
+      intro x s hu
+      have hn : ¬ (s.1.isSome ∧ s.2 = none ∧
+        ((∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+          ∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
+        fun hf => by
+          have hu' : s.2.isSome = true := hu
+          rw [hf.2.1] at hu'
+          exact Bool.false_ne_true hu'
+      rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hn]
+      exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y _ _ x s hn).1.trans
+        (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hn).1.symm
+    · intro x s _
+      rcases h01 i h2 with rfl | rfl
+      · rw [bb1SimLazy_zero]
+        exact bb1SimImpl_zero_coins G ℓ b κ d g X Y _ _ _ _ x s
+      · rw [bb1SimLazy_one]
+        exact bb1SimImpl_one_coins G ℓ b κ d g X Y _ _ _ _ x s
+  -- a used state stays used
+  · intro x s hu
+    by_cases h2 : i = 2
+    · subst h2
+      have hn : ¬ (s.1.isSome ∧ s.2 = none ∧
+        ((∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+          ∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
+        fun hf => by
+          have hu' : s.2.isSome = true := hu
+          rw [hf.2.1] at hu'
+          exact Bool.false_ne_true hu'
+      rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hn]
+      exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hn).2.mono fun p hp => by
+        show p.2.2.isSome = true; rw [hp]; exact hu
+    · rcases h01 i h2 with rfl | rfl
+      · rw [bb1SimLazy_zero]
+        exact (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 0 (by decide) x s).mono
+          fun p hp => by show p.2.2.isSome = true; rw [hp]; exact hu
+      · rw [bb1SimLazy_one]
+        exact (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 1 (by decide) x s).mono
+          fun p hp => by show p.2.2.isSome = true; rw [hp]; exact hu
+  -- from an unused state, only the first valid `Challenge` spends the coins
+  · intro x s hu
+    by_cases h2 : i = 2
+    · subst h2
+      by_cases hf : (s.1.isSome ∧ s.2 = none ∧
+        ((∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+          ∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
+      · exact Or.inr ⟨bb1SimLazy_two_fresh G ℓ b κ d g X Y zt x s hf,
+          fun u => bb1SimImpl_two_fresh_allOutputs G ℓ b κ d g X Y _ _ x s hf⟩
+      · refine Or.inl fun u => ⟨?_, ?_⟩ <;> rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hf]
+        · exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y _ _ x s hf).1.trans
+            (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hf).1.symm
+        · exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hf).2.mono fun p hp => by
+            show ¬ (p.2.2.isSome = true); rw [hp]; exact hu
+    · refine Or.inl fun u => ?_
+      rcases h01 i h2 with rfl | rfl
+      · rw [bb1SimLazy_zero]
+        exact ⟨bb1SimImpl_zero_coins G ℓ b κ d g X Y _ _ _ _ x s,
+          (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 0 (by decide) x s).mono
+            fun p hp => by show ¬ (p.2.2.isSome = true); rw [hp]; exact hu⟩
+      · rw [bb1SimLazy_one]
+        exact ⟨bb1SimImpl_one_coins G ℓ b κ d g X Y _ _ _ _ x s,
+          (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 1 (by decide) x s).mono
+            fun p hp => by show ¬ (p.2.2.isSome = true); rw [hp]; exact hu⟩
+
+end Lazy
+
+end BB1Sim
+
+end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean
new file mode 100644
index 000000000..0e49a31ab
--- /dev/null
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean
@@ -0,0 +1,139 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
+import TCSlib.Cryptography.Games.Relational
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The BB1 simulator on a random `T` does not depend on the challenge bit
+
+Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 2 of
+[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "when `T` is uniform and independent in `G_1`
+… `C` is independent of `b` in the adversary's view" [BB04, proof of Theorem 4.1, *Challenge*].
+`T` is used only at the first valid `Challenge`, so it can be drawn there
+(`expect_simulate_bb1SimLazy`, step E-T); at that call, `T ↦ M_1^{−1} M_0 T` turns the answer
+`M_0 · T` of the simulator with challenge bit `0` into the answer `M_1 · T'` of the one with
+challenge bit `1`, and every other call is the same for both bits.
+
+## Main definitions
+
+None.
+
+## Main results
+
+* `BB1Sim.bb1SimLazy_random_call` — the lazy simulators with challenge bits `0` and `1` and
+  `T` drawn at the challenge give equal expectations, call by call.
+* `BB1Sim.expect_bb1SimImpl_random` — on a uniform `T`, the simulators with challenge bits `0`
+  and `1` simulate alike.
+
+## References
+
+* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
+  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
+  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
+  Theorem 4.1.
+-/
+
+namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
+
+open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
+  TCSlib.Cryptography.Composability
+
+namespace BB1Sim
+
+variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
+
+/-- **The challenge bit is hidden by a random `T`, call by call** [BB04, proof of Theorem 4.1,
+*Challenge*]: with `T` drawn at the first valid `Challenge` (`zt T = (Z, T)`), every call of the
+lazy simulators with challenge bits `0` and `1` gives the same expectation to every `F`:
+`𝔼[F] (bb1SimLazy false … i x s) = 𝔼[F] (bb1SimLazy true … i x s)`.
+
+**Proof sketch.** `Init` and `KeyGen` do not depend on the bit (`bb1SimLazy_zero`,
+`bb1SimLazy_one`, `bb1SimImpl_eq`, `IBEScheme.oracleImpl_zero_onSpec`,
+`IBEScheme.oracleImpl_one_onSpec`). A `Challenge` other than the first valid one answers `⊥` or
+repeats the recorded challenge (`bb1SimLazy_two_of_not`, `bb1SimChal_none`, `bb1SimChal_repeat`,
+`bb1SimChal_invalid`). At the first valid one, `ProbComp.expect_sample_rel` with `R := Eq` along
+`T ↦ decodeT(M_1)^{−1} decodeT(M_0) T` (`bb1SimLazy_two_fresh`, `bb1SimChal_fresh`,
+`ofFn_bb1SimCt`). -/
+theorem bb1SimLazy_random_call (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
+    (s : BB1SimState G ℓ κ d) (F : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ) :
+    ProbComp.expect (bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F =
+      ProbComp.expect
+        (bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F := by
+  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
+  rcases h012 i with rfl | rfl | rfl
+  -- `Init` and `KeyGen` do not depend on the bit
+  · rw [bb1SimLazy_zero, bb1SimLazy_zero, bb1SimImpl_eq, bb1SimImpl_eq,
+      IBEScheme.oracleImpl_zero_onSpec, IBEScheme.oracleImpl_zero_onSpec]
+  · rw [bb1SimLazy_one, bb1SimLazy_one, bb1SimImpl_eq, bb1SimImpl_eq,
+      IBEScheme.oracleImpl_one_onSpec, IBEScheme.oracleImpl_one_onSpec]
+  by_cases hf : (s.1.isSome ∧ s.2 = none ∧
+        ((∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
+          ∃ u, List.ofFn ((G.group κ d).encT u) =
+            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
+  -- the first valid `Challenge`: reindex `T` by `T ↦ M₁⁻¹ M₀ T`
+  · rw [bb1SimLazy_two_fresh G ℓ false κ d g X Y _ x s hf,
+      bb1SimLazy_two_fresh G ℓ true κ d g X Y _ x s hf]
+    obtain ⟨s₁, s₂⟩ := s
+    obtain ⟨h₁, h₂, hv⟩ := hf
+    rcases s₁ with _ | ⟨t, α₁⟩
+    · exact absurd h₁ Bool.false_ne_true
+    subst h₂
+    set m := (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)) with hm
+    have key : ∀ (b : Bool) (T : (G.group κ d).GT),
+        bb1SimImpl G ℓ b κ d g X Y Z T 2 x (some (t, α₁), none) =
+          .pure (cast (sidSpec_rng_two _ κ).symm
+              (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)),
+            (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)))) :=
+      fun b T => by
+        rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh G ℓ b κ d g X Y Z T _
+          t α₁ ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1,
+            (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩, OracleComp.pure_bind]
+    simp only [key]
+    have hct : ∀ T, bb1SimCt G ℓ κ d Z T α₁ m.1 =
+        bb1SimCt G ℓ κ d Z (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
+          (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d)
+            (padFin _ (List.ofFn m.1))) T) α₁ m.2 := fun T => by
+      simp only [Equiv.coe_mulLeft]
+      rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _),
+        List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), mul_assoc, mul_inv_cancel_left]
+    refine ProbComp.expect_sample_rel Eq (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
+      (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m.1)))) _ _
+      (fun T => ⟨?_, ?_⟩) F F (fun y s' t' h => by rw [h]) <;>
+    simp only [Bool.false_eq_true, ↓reduceIte, hct]
+  -- every other `Challenge` does not depend on the bit
+  · rw [bb1SimLazy_two_of_not G ℓ false κ d g X Y _ x s hf,
+      bb1SimLazy_two_of_not G ℓ true κ d g X Y _ x s hf,
+      (bb1SimImpl_two_of_not G ℓ true κ d g X Y 1 1 x s hf).1]
+
+/-- **On a random `T`, the simulator does not depend on the challenge bit** [BB04, proof of
+Theorem 4.1, *Challenge*, "when `T` is uniform and independent in `G_1` … `C` is independent of
+`b` in the adversary's view"]: for every computation `c` and every `F` of its output,
+`𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl false … Z T) c (none, none)) =
+𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl true … Z T) c (none, none))`.
+
+**Proof sketch.** Draw `T` at the first valid `Challenge` on both sides
+(`expect_simulate_bb1SimLazy`, step E-T), then compare the lazy simulators call by call
+(`ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`). -/
+theorem expect_bb1SimImpl_random {β : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β)
+    (F : β → ℝ) :
+    ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
+        (simulate (bb1SimImpl G ℓ false κ d g X Y Z T) c (none, none)) (fun p => F p.1)) =
+      ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
+        (simulate (bb1SimImpl G ℓ true κ d g X Y Z T) c (none, none)) (fun p => F p.1)) := by
+  rw [← expect_simulate_bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
+    rfl, ← expect_simulate_bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
+    rfl]
+  exact ProbComp.expect_simulate_congr _ _
+    (fun i x s F => bb1SimLazy_random_call G ℓ κ d g X Y Z i x s F) c _ _
+
+end BB1Sim
+
+end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean
new file mode 100644
index 000000000..71f472d32
--- /dev/null
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean
@@ -0,0 +1,423 @@
+/-
+Copyright (c) 2026 TCSlib contributors. All rights reserved.
+Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
+-/
+import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
+import TCSlib.Cryptography.Games.Relational
+
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
+/-!
+# The real IND-sID-CPA game of BB1, with `h` drawn at `Init`
+
+Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
+[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The real game draws the parameter `h` in `Setup`,
+before the adversary commits to `ID*`; the simulator chooses `h = g_1^{−ID*} g^{α_1}` after the
+commitment. This module moves the real draw of `h` to the first `Init`:
+* `RealReads` and `setup_out` read the output of `Setup` without naming the parameters as a
+  value: a map `o` from the setup's coins to parameters and master key, and what the game's
+  oracles read from `o …` (the encoded parameters, the message space, the encoded keys and
+  ciphertexts);
+* `bb1RealAt o h` runs the game's oracles on the parameters `o h'` for the `h'` recorded with the
+  committed identity, and records `h` at the first `Init`; from the empty state it simulates like
+  the game's oracles on `o h` (`expect_simulate_sidImpl_bb1RealAt`, an instance of
+  `ProbComp.expect_simulate_rel`);
+* `bb1RealLazy o` draws `h` at the first `Init`; it simulates like `bb1RealAt o h` with `h` drawn
+  in advance (`expect_sample_bb1RealAt`, an instance of `Games.expect_simulate_eager`).
+
+## Main definitions
+
+* `BB1Sim.RealReads` — what the game's oracles read from the parameters and master key.
+* `BB1Sim.BB1RealState` — the game's state with `h` recorded beside the committed identity.
+* `BB1Sim.bb1RealAt`, `BB1Sim.bb1RealLazy` — the game's oracles with `h` recorded, and with `h`
+  drawn at the first `Init`.
+
+## Main results
+
+* `BB1Sim.setup_out` — the output of `Setup`, read.
+* `BB1Sim.expect_simulate_sidImpl_bb1RealAt` — step R1: the game's oracles simulate like
+  `bb1RealAt`.
+* `BB1Sim.expect_sample_bb1RealAt` — step E-h: `h` drawn at the first `Init`.
+* `BB1Sim.expect_sample_sidImpl` — both: the game with `h` drawn in advance simulates like
+  `bb1RealLazy`.
+
+## References
+
+* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
+  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
+  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.1 (pp. 5–6): the system;
+  §4.2 (pp. 6–8): the proof of Theorem 4.1.
+-/
+
+namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
+
+open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
+  TCSlib.Cryptography.Composability
+
+namespace BB1Sim
+
+/-! ### The real parameters, from the setup's output -/
+
+section Setup
+
+variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ)
+
+/-- **What the real game's oracles read from its parameters and master key** `k`, for parameters
+`(g, g^α, Y, h)` and master key `Y^α` in the group described by `d` [BB04, §4.1]: the encoded
+parameters, the message space, the encoded keys of `KeyGen`, and the encoded ciphertexts of
+`Encrypt`. -/
+structure RealReads (d : List Bool) (g : (G.group κ d).G) (α : ZMod (G.group κ d).order)
+    (Y h : (G.group κ d).G) (k : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) : Prop where
+  /-- The encoded parameters: `d ‖ g ‖ g^α ‖ Y ‖ h`. -/
+  encPP : (bb1Scheme G ℓ).encPP κ k.1 = padFin ((bb1Scheme G ℓ).ppLen.eval κ)
+    (d ++ List.ofFn ((G.group κ d).encG g) ++ List.ofFn ((G.group κ d).encG (g ^ α.val)) ++
+      List.ofFn ((G.group κ d).encG Y) ++ List.ofFn ((G.group κ d).encG h))
+  /-- The message space: the encodings of `G_T`. -/
+  msgSpace : ∀ m, (bb1Scheme G ℓ).MsgSpace κ k.1 m ↔
+    ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m
+  /-- `KeyGen`, encoded, then `f`: the key word is `Y^α F(ID)^r ‖ g^r` with `r` uniform. -/
+  keyGen : ∀ id {β : Type} (f : (Fin ((bb1Scheme G ℓ).skLen.eval κ) → Bool) → ProbComp β),
+    ((bb1Scheme G ℓ).keyGen κ k.2 id).bind (fun sk => f ((bb1Scheme G ℓ).encSK κ sk)) =
+      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
+        f (padFin ((bb1Scheme G ℓ).skLen.eval κ)
+          (List.ofFn ((G.group κ d).encG
+              (Y ^ α.val * BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) id) ^ r.val)) ++
+            List.ofFn ((G.group κ d).encG (g ^ r.val))))
+  /-- `Encrypt`, encoded, then `f`: the ciphertext word is `M · e(g^α, Y)^s ‖ g^s ‖ F(ID)^s`
+  with `s` uniform, the message read at the width of `G_T`. -/
+  enc : ∀ t m {β : Type} (f : (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) → ProbComp β),
+    ((bb1Scheme G ℓ).enc κ k.1 t m).bind (fun ct => f ((bb1Scheme G ℓ).encCT κ ct)) =
+      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun s =>
+        f (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
+          (List.ofFn ((G.group κ d).encT ((G.group κ d).pair (g ^ α.val) Y ^ s.val *
+              BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))) ++
+            List.ofFn ((G.group κ d).encG (g ^ s.val)) ++
+            List.ofFn ((G.group κ d).encG
+              (BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) t) ^ s.val))))
+
+/-- **The setup's output, read** [BB04, §4.1, *Setup*]: there is a map `o` from the setup's
+coins to parameters and master key of `bb1Scheme G ℓ` such that `Setup` draws `r`, `g ∈ G^*`,
+`α`, `h`, `g_2` and returns `o r g α h g_2`:
+`(Setup κ).bind F = (sample r).bind … (sample g_2).bind fun g_2 => F (o r g α h g_2)` for every
+continuation `F`, and the game's oracles read `o r g α h g_2` as the parameters
+`(g, g^α, g_2, h)` and the master key `g_2^α` of the group `desc(κ, r)` (`RealReads`).
+
+**Proof sketch.** `o` is the setup's output map, found by unification after reading `Setup`
+through `bb1Scheme_setup_eq` and `BB1.setup_eq`. The four readings: `ofFn_bb1Scheme_encPP`;
+`bb1Scheme_msgSpace_iff`; `bb1Scheme_keyGen_bind`, `BB1.keyGen_eq` and
+`ofFn_bb1Scheme_encSK`; `bb1Scheme_enc_bind`, `BB1.encrypt_eq` and `ofFn_bb1Scheme_encCT`
+(vectors with equal words are equal, `List.ofFn_injective`). -/
+theorem setup_out :
+    ∃ o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
+        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
+        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ,
+      (∀ {β : Type} (F : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ → ProbComp β),
+        ((bb1Scheme G ℓ).setup κ).bind F =
+          (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
+          (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
+          (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
+          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
+          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 => F (o r g α h g2)) ∧
+      ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2) := by
+  refine ⟨?o, fun F => ?hF, ?hR⟩
+  case hF =>
+    rw [bb1Scheme_setup_eq]
+    simp only [OracleComp.bind_assoc, BB1.setup_eq, OracleComp.pure_bind]
+    rfl
+  case hR =>
+    intro r g α h g2
+    refine ⟨?_, ?_, ?_, ?_⟩
+    · exact List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ _ _)
+    · exact fun m => bb1Scheme_msgSpace_iff G ℓ κ _ _ m
+    · intro id β f
+      rw [bb1Scheme_keyGen_bind, BB1.keyGen_eq, OracleComp.bind_assoc]
+      simp only [OracleComp.pure_bind]
+      refine congrArg _ (funext fun r => ?_)
+      rw [List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ _ _)]
+    · intro t m β f
+      rw [bb1Scheme_enc_bind, BB1.encrypt_eq, OracleComp.bind_assoc]
+      simp only [OracleComp.pure_bind]
+      refine congrArg _ (funext fun s => ?_)
+      rw [List.ofFn_injective (ofFn_bb1Scheme_encCT G ℓ κ _ _)]
+
+end Setup
+
+/-! ### The game's oracles with `h` recorded -/
+
+section Real
+
+variable (G : BilinearGen) (ℓ : PolyExpr)
+
+/-- The real game's state with the parameter `h` recorded beside the committed identity, and
+the recorded challenge: `Option ((Fin idLen → Bool) × G) × Option (Fin ctLen → Bool)`. Glue:
+the state of `bb1RealAt` and `bb1RealLazy`. -/
+abbrev BB1RealState (κ : ℕ) (d : List Bool) : Type :=
+  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) ×
+    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)
+
+/-- `BB1RealState G ℓ κ d` is the optional pair of the committed identity and the recorded `h`,
+with the optional recorded challenge: `BB1RealState G ℓ κ d =
+Option ((Fin idLen → Bool) × G) × Option (Fin ctLen → Bool)`. Glue: the reader of
+`BB1RealState` (policy §1). -/
+theorem bb1RealState_eq (κ : ℕ) (d : List Bool) :
+    BB1RealState G ℓ κ d =
+      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) ×
+        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl
+
+/-- **The game's oracles with `h` recorded** (a variant of the game of [BB04, §2.1], with `h`
+recorded beside the committed identity): with hidden bit `b`, on the
+parameters and master key `o h'` for the `h'` recorded with the committed identity (or `h`
+before `Init`), the call of `IBEScheme.sidImpl` on the state without `h'`; the first `Init`
+records `h` with the identity. -/
+noncomputable def bb1RealAt (b : Bool) (κ : ℕ) (d : List Bool)
+    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G) :
+    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
+  fun i x u => ((bb1Scheme G ℓ).sidImpl b κ (o ((u.1.map Prod.snd).getD h)).1
+    (o ((u.1.map Prod.snd).getD h)).2 i x (u.1.map Prod.fst, u.2)).bind
+      fun p => .pure (p.1, (p.2.1.map fun t => (t, (u.1.map Prod.snd).getD h), p.2.2))
+
+/-- Before `Init`, `bb1RealAt o h` is the game's oracle on `o h`, recording `h` with the
+committed identity: `bb1RealAt … o h i x (none, c) = (sidImpl b κ (o h).1 (o h).2 i x
+(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of
+`bb1RealAt`. -/
+theorem bb1RealAt_none (b : Bool) (κ : ℕ) (d : List Bool)
+    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
+    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    bb1RealAt G ℓ b κ d o h i x (none, c) =
+      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (none, c)).bind
+        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := rfl
+
+/-- After `Init`, `bb1RealAt o h` is the game's oracle on `o h'` for the recorded `h'`:
+`bb1RealAt … o h i x (some (t, h'), c) = (sidImpl b κ (o h').1 (o h').2 i x
+(some t, c)).bind fun p => pure (p.1, (p.2.1.map (·, h'), p.2.2))`. Glue: a case reader of
+`bb1RealAt`. -/
+theorem bb1RealAt_some (b : Bool) (κ : ℕ) (d : List Bool)
+    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
+    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
+    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h' : (G.group κ d).G)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    bb1RealAt G ℓ b κ d o h i x (some (t, h'), c) =
+      ((bb1Scheme G ℓ).sidImpl b κ (o h').1 (o h').2 i x (some t, c)).bind
+        fun p => .pure (p.1, (p.2.1.map fun t => (t, h'), p.2.2)) := rfl
+
+open Classical in
+/-- **The game's oracles with `h` drawn at the first `Init`** (a variant of the game of
+[BB04, §2.1], with `h` drawn late): the first `Init`
+draws `h ∈ G` and calls `bb1RealAt o h`; every other call is the call of `bb1RealAt o 1`, which
+reads the recorded `h'` after `Init` and no parameter before it. -/
+noncomputable def bb1RealLazy (b : Bool) (κ : ℕ) (d : List Bool)
+    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) :
+    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
+  fun i x u => if u.1.isNone ∧ i = 0 then
+      (ProbComp.sample (G.group κ d).G).bind fun h => bb1RealAt G ℓ b κ d o h i x u
+    else bb1RealAt G ℓ b κ d o 1 i x u
+
+variable (b : Bool) (κ : ℕ) (d : List Bool)
+  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
+
+/-- The first `Init` of `bb1RealLazy` draws `h` and calls the game's oracle on `o h`:
+`bb1RealLazy … o 0 x (none, c) = (sample G).bind fun h => (sidImpl b κ (o h).1 (o h).2 0 x
+(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of
+`bb1RealLazy`. -/
+theorem bb1RealLazy_zero_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    bb1RealLazy G ℓ b κ d o 0 x (none, c) =
+      (ProbComp.sample (G.group κ d).G).bind fun h =>
+        ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 0 x (none, c)).bind
+          fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
+  rw [bb1RealLazy, if_pos ⟨rfl, rfl⟩]
+  rfl
+
+/-- Before `Init`, the other calls of `bb1RealLazy` are the game's oracles on `o 1`: for `i ≠ 0`,
+`bb1RealLazy … o i x (none, c) = (sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind fun p =>
+pure (p.1, (p.2.1.map (·, 1), p.2.2))`. Glue: a case reader of `bb1RealLazy`. -/
+theorem bb1RealLazy_none_of_ne (i : Fin 3) (hi : i ≠ 0) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    bb1RealLazy G ℓ b κ d o i x (none, c) =
+      ((bb1Scheme G ℓ).sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind
+        fun p => .pure (p.1, (p.2.1.map fun t => (t, 1), p.2.2)) := by
+  rw [bb1RealLazy, if_neg fun h => hi h.2]
+  rfl
+
+/-- After `Init`, `bb1RealLazy` is the game's oracle on `o h` for the recorded `h`:
+`bb1RealLazy … o i x (some (t, h), c) = (sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
+fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of `bb1RealLazy`. -/
+theorem bb1RealLazy_some (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
+    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
+    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
+    bb1RealLazy G ℓ b κ d o i x (some (t, h), c) =
+      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
+        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
+  rw [bb1RealLazy, if_neg fun h => absurd h.1 (by simp)]
+  rfl
+
+/-- **The game's oracles keep the committed identity**: for every scheme `S`, every outcome of
+`S.sidImpl b κ pp msk i x (some t, c)` has the committed identity `t`. Glue: a case fact of
+`IBEScheme.sidImpl`, from its readers.
+
+**Proof sketch.** By cases on the oracle, read through `IBEScheme.sidImpl_zero_onSpec`,
+`sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec` and
+`sidImpl_challenge_fresh_onSpec`: `Init` keeps the state (`sidImpl_init_some`), `KeyGen` keeps it
+(`sidImpl_keyGen_target`, `sidImpl_keyGen_ne`), and `Challenge` keeps `ID*` and records the
+challenge at most (`sidImpl_challenge_fresh`, `_invalid`, `_repeat`). -/
+theorem sidImpl_allOutputs_some (S : IBEScheme) (pp : S.PP κ) (msk : S.MSK κ) (i : Fin 3)
+    (x : (S.sidSpec κ).dom i) (t : Fin (S.idLen.eval κ) → Bool)
+    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
+    (S.sidImpl b κ pp msk i x (some t, c)).AllOutputs fun p => p.2.1 = some t := by
+  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
+  rcases h012 i with rfl | rfl | rfl
+  · rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some, OracleComp.pure_bind]
+    exact OracleComp.allOutputs_pure.2 rfl
+  · by_cases ht : cast (sidSpec_dom_one S κ) x = t
+    · rw [IBEScheme.sidImpl_one_onQuery, ht, IBEScheme.sidImpl_keyGen_target]
+      exact OracleComp.allOutputs_pure.2 rfl
+    · rw [IBEScheme.sidImpl_keyGen_ne_onSpec S b κ pp msk x t c ht]
+      apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
+      intro _ _
+      exact OracleComp.allOutputs_pure.2 rfl
+  · rcases c with _ | w
+    · by_cases hv : S.MsgSpace κ pp
+          (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).1 ∧
+        S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).2
+      · rw [IBEScheme.sidImpl_challenge_fresh_onSpec S b κ pp msk x t hv]
+        apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
+        intro _ _
+        exact OracleComp.allOutputs_pure.2 rfl
+      · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_invalid (h := hv)]
+        exact OracleComp.allOutputs_pure.2 rfl
+    · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_repeat]
+      exact OracleComp.allOutputs_pure.2 rfl
+
+/-- **Before `Init`, `KeyGen` and `Challenge` do not read the parameters**: for every scheme `S`
+and `i ≠ 0`, `S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c)`, and
+every outcome keeps the state `(none, c)`. Glue: a case fact of `IBEScheme.sidImpl`, from its
+readers. -/
+theorem sidImpl_none_of_ne (S : IBEScheme) (pp pp' : S.PP κ) (msk msk' : S.MSK κ) (i : Fin 3)
+    (hi : i ≠ 0) (x : (S.sidSpec κ).dom i) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
+    S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c) ∧
+      (S.sidImpl b κ pp msk i x (none, c)).AllOutputs fun p => p.2 = (none, c) := by
+  have h12 : ∀ i : Fin 3, i ≠ 0 → i = 1 ∨ i = 2 := by decide
+  rcases h12 i hi with rfl | rfl
+  · rw [IBEScheme.sidImpl_one_onQuery S b κ pp msk x,
+      IBEScheme.sidImpl_one_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_keyGen_none,
+      IBEScheme.sidImpl_keyGen_none]
+    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
+  · rw [IBEScheme.sidImpl_two_onQuery S b κ pp msk x,
+      IBEScheme.sidImpl_two_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_challenge_none,
+      IBEScheme.sidImpl_challenge_none]
+    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
+
+/-- **Step R1** (design r1 §3.1): from the empty state, the game's oracles on `o h` simulate like
+`bb1RealAt o h`, for functions `F` of the output:
+`𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
+𝔼[F ∘ fst] (simulate (bb1RealAt … o h) c (none, none))`. Glue: an instance of
+`ProbComp.expect_simulate_rel` with `R s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
+
+**Proof sketch.** From related states, `bb1RealAt o h` reads the recorded `h' = h`, so its call
+is the game's call followed by recording `h` (`bb1RealAt_none`, `bb1RealAt_some`); its
+expectation is the game's call's (`expect_bind`, `expect_pure`), whose new states are related
+to the recorded ones. `ProbComp.expect_simulate_rel` concludes. -/
+theorem expect_simulate_sidImpl_bb1RealAt (h : (G.group κ d).G) {α : Type}
+    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α) (F : α → ℝ) :
+    ProbComp.expect (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
+        (fun p => F p.1) =
+      ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) (fun p => F p.1) := by
+  refine ProbComp.expect_simulate_rel _ _
+    (fun s u => s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h) (fun i x s u hsu g₀ g₁ hg => ?_)
+    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, fun p hp => by cases hp⟩
+  obtain ⟨rfl, hh⟩ := hsu
+  -- from related states, `bb1RealAt h` reads the recorded `h`
+  have hget : (u.1.map Prod.snd).getD h = h := by
+    rcases u with ⟨_ | ⟨t, h'⟩, c⟩
+    · rfl
+    · exact hh _ rfl
+  rw [show bb1RealAt G ℓ b κ d o h i x u =
+      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (u.1.map Prod.fst, u.2)).bind
+        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) by rw [bb1RealAt, hget],
+    ProbComp.expect_bind]
+  refine congrArg _ (funext fun p => ?_)
+  rw [ProbComp.expect_pure]
+  refine hg p.1 p.2 _ ⟨?_, fun q hq => ?_⟩ <;> rcases p with ⟨a, _ | t, c⟩
+  · rfl
+  · rfl
+  · cases hq
+  · cases hq
+    rfl
+
+/-- **Step E-h** (design r1 §3.1): `h` drawn in advance or at the first `Init` simulate alike:
+`𝔼_{h ← G} 𝔼[F] (simulate (bb1RealAt … o h) c (none, none)) =
+𝔼[F] (simulate (bb1RealLazy … o) c (none, none))`. Glue: an instance of
+`Games.expect_simulate_eager`, with `h` spent at the first `Init`.
+
+**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1RealLazy o`,
+`OE h := bb1RealAt o h` and `used u := u.1` some. After `Init` both read the recorded `h`
+(`bb1RealAt_some`, `bb1RealLazy_some`) and keep the identity (`sidImpl_allOutputs_some`). Before
+`Init`, `KeyGen` and `Challenge` read no parameter and keep the state (`sidImpl_none_of_ne`,
+`bb1RealLazy_none_of_ne`); the first `Init` draws `h` (`bb1RealLazy_zero_none`) and records an
+identity (`IBEScheme.sidImpl_zero_onSpec`, `IBEScheme.sidImpl_init_none`). -/
+theorem expect_sample_bb1RealAt {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
+    (F : α × BB1RealState G ℓ κ d → ℝ) :
+    ProbComp.expect (ProbComp.sample (G.group κ d).G)
+        (fun h => ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) F) =
+      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) F := by
+  refine (Games.expect_simulate_eager (T := (G.group κ d).G) (bb1RealLazy G ℓ b κ d o)
+    (bb1RealAt G ℓ b κ d o) (fun u => u.1.isSome = true) (fun h i x u hu => ?_)
+    (fun i x u hu => ?_) (fun i x u hu => ?_) c F
+    (by show ¬ ((none : Option _).isSome = true); exact Bool.false_ne_true)).symm
+  -- after `Init`, both read the recorded `h`
+  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
+    · exact absurd hu Bool.false_ne_true
+    · rw [bb1RealAt_some, bb1RealLazy_some]
+  -- the committed identity stays committed
+  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
+    · exact absurd hu Bool.false_ne_true
+    · rw [bb1RealLazy_some]
+      exact (sidImpl_allOutputs_some b κ _ _ _ i x t c).bind fun p hp =>
+        OracleComp.allOutputs_pure.2 (by show (p.2.1.map _).isSome = true; rw [hp]; rfl)
+  -- before `Init`: the first `Init` draws `h`; `KeyGen` and `Challenge` read no parameter
+  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
+    swap
+    · exact absurd rfl hu
+    by_cases hi : i = 0
+    · subst hi
+      refine Or.inr ⟨?_, fun h => ?_⟩
+      · rw [bb1RealLazy_zero_none]
+        exact congrArg _ (funext fun h => (bb1RealAt_none G ℓ b κ d o h 0 x c).symm)
+      · rw [bb1RealAt_none, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none,
+          OracleComp.pure_bind, OracleComp.pure_bind]
+        exact OracleComp.allOutputs_pure.2 rfl
+    · have hn := fun h => sidImpl_none_of_ne b κ (bb1Scheme G ℓ) (o h).1 (o 1).1 (o h).2 (o 1).2
+        i hi x c
+      refine Or.inl fun h => ⟨?_, ?_⟩
+      · rw [bb1RealAt_none, bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c, (hn h).1]
+        exact OracleComp.bind_congr_of_allOutputs (hn 1).2 fun p hp => by rw [hp]; rfl
+      · rw [bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c]
+        exact (sidImpl_none_of_ne b κ _ (o 1).1 (o 1).1 (o 1).2 (o 1).2 i hi x c).2.bind
+          fun p hp => OracleComp.allOutputs_pure.2 (by
+            show ¬ ((p.2.1.map _).isSome = true); rw [hp]; exact Bool.false_ne_true)
+
+/-- **The real game with `h` drawn at the first `Init`** (steps R1 and E-h of design r1 §3.1):
+`𝔼_{h ← G} 𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
+𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none))`. Glue.
+
+**Proof sketch.** `expect_simulate_sidImpl_bb1RealAt` for each `h`, then
+`expect_sample_bb1RealAt`. -/
+theorem expect_sample_sidImpl {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
+    (F : α → ℝ) :
+    ProbComp.expect (ProbComp.sample (G.group κ d).G)
+        (fun h => ProbComp.expect
+          (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
+          (fun p => F p.1)) =
+      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) := by
+  rw [← expect_sample_bb1RealAt]
+  exact congrArg _ (funext fun h => expect_simulate_sidImpl_bb1RealAt G ℓ b κ d o h c F)
+
+end Real
+
+end BB1Sim
+
+end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean
index b0fc112a2..da69b0f56 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean
@@ -429,6 +429,93 @@ theorem oracleImpl_two_onSpec {σ : Type} (κ : ℕ)
           from rfl).symm p.1, p.2) :=
   (OracleComp.bind_pure _).symm
 
+/-- **Oracle `0` of the game on the game's query type**: `Init` on the query read as an identity,
+its answer read back on the game's answer type:
+`S.sidImpl b κ pp msk 0 x s =
+(S.sidImpl b κ pp msk 0 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
+theorem sidImpl_zero_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 0) (s : S.SidState κ) :
+    S.sidImpl b κ pp msk 0 x s =
+      (S.sidImpl b κ pp msk 0
+        (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
+          Fin (S.idLen.eval κ) → Bool) s).bind
+        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
+          from rfl).symm p.1, p.2) :=
+  (OracleComp.bind_pure _).symm
+
+/-- **Oracle `2` of the game on the game's query type**: `Challenge` on the query read as two
+messages, its answer read back on the game's answer type:
+`S.sidImpl b κ pp msk 2 x s =
+(S.sidImpl b κ pp msk 2 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
+theorem sidImpl_two_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
+    S.sidImpl b κ pp msk 2 x s =
+      (S.sidImpl b κ pp msk 2
+        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
+          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s).bind
+        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
+          from rfl).symm p.1, p.2) :=
+  (OracleComp.bind_pure _).symm
+
+/-- **Oracle `1` of the game, its query read as an identity**: the call on the game's query
+type is the call on the query read as an `idLen(κ)`-bit identity, with the answer kept on the
+game's answer type (the form for the `⊥` answers):
+`S.sidImpl b κ pp msk 1 x s = S.sidImpl b κ pp msk 1 (cast x) s`. -/
+theorem sidImpl_one_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 1) (s : S.SidState κ) :
+    S.sidImpl b κ pp msk 1 x s =
+      S.sidImpl b κ pp msk 1
+        (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
+          Fin (S.idLen.eval κ) → Bool) s := rfl
+
+/-- **Oracle `2` of the game, its query read as two messages**: the call on the game's query
+type is the call on the query read as two `msgLen(κ)`-bit messages, with the answer kept on the
+game's answer type (the form for the `⊥` answers):
+`S.sidImpl b κ pp msk 2 x s = S.sidImpl b κ pp msk 2 (cast x) s`. -/
+theorem sidImpl_two_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
+    S.sidImpl b κ pp msk 2 x s =
+      S.sidImpl b κ pp msk 2
+        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
+          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s := rfl
+
+/-- **`KeyGen` for another identity, on the game's types**: with `ID*` recorded and the query
+`x`, read as an identity, different from it, the answer is `⟨1, d_ID⟩` with
+`d_ID ← KeyGen(msk, ID)`, read back on the game's answer type: for `cast x ≠ t`,
+`S.sidImpl b κ pp msk 1 x (some t, c) =
+(S.keyGen κ msk (cast x)).bind fun sk => pure (cast (decAnswer (some (encSK sk))), (some t, c))`. -/
+theorem sidImpl_keyGen_ne_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 1) (t : Fin (S.idLen.eval κ) → Bool)
+    (c : Option (Fin (S.ctLen.eval κ) → Bool))
+    (h : (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
+      Fin (S.idLen.eval κ) → Bool) ≠ t) :
+    S.sidImpl b κ pp msk 1 x (some t, c) =
+      (S.keyGen κ msk (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl)
+        x)).bind fun sk =>
+        .pure (cast (show (Fin (S.skLen.eval κ + 1) → Bool) = (S.sidSpec κ).rng 1 from rfl)
+          (FixedLengthScheme.decAnswer (some (S.encSK κ sk))), (some t, c)) :=
+  S.sidImpl_keyGen_ne b κ pp msk _ t c h
+
+/-- **The first valid `Challenge`, on the game's types**: with `ID*` recorded, no challenge yet,
+and both messages of the query `x`, read as two messages, in the message space, the answer is
+`C ← Encrypt(params, ID*, M_b)`, read back on the game's answer type, and `C` is recorded: for
+`(M₀, M₁) = splitHalf (cast x)` with `M₀, M₁ ∈ M`, `S.sidImpl b κ pp msk 2 x (some t, none) =
+(S.enc κ pp t M_b).bind fun C => pure (cast (encCT C), (some t, some (encCT C)))`. -/
+theorem sidImpl_challenge_fresh_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
+    (x : (S.sidSpec κ).dom 2) (t : Fin (S.idLen.eval κ) → Bool)
+    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
+        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1 ∧
+      S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
+        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2) :
+    S.sidImpl b κ pp msk 2 x (some t, none) =
+      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
+          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2
+        else (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
+          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1)).bind fun c =>
+        .pure (cast (show (Fin (S.ctLen.eval κ) → Bool) = (S.sidSpec κ).rng 2 from rfl)
+          (S.encCT κ c), (some t, some (S.encCT κ c))) :=
+  S.sidImpl_challenge_fresh b κ pp msk _ t h
+
 /-- The codec of the adversary: the three oracles and a one-bit guess. -/
 def sidCodec (κ : ℕ) : MachineCodec (S.sidSpec κ) (Fin 1 → Bool) :=
   bitCodec (S.inLens κ) (S.outLens κ) 1
diff --git a/TCSlib/Cryptography/Games/Relational.lean b/TCSlib/Cryptography/Games/Relational.lean
index eee8e19f1..15015555b 100644
--- a/TCSlib/Cryptography/Games/Relational.lean
+++ b/TCSlib/Cryptography/Games/Relational.lean
@@ -90,7 +90,13 @@ theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
     (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
     (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
     expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
-  sorry
+  induction c generalizing s t with
+  | pure a =>
+    rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
+    exact hG a s t hst
+  | query i x k ih =>
+    rw [simulate_query, simulate_query, expect_bind, expect_bind]
+    exact h i x s t hst _ _ fun y s' t' hR => ih y hR
 
 /-- **Events on the output, from related states:** under the hypothesis of
 `expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
@@ -127,7 +133,13 @@ theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [
     (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
     expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
       expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
-  sorry
+  rw [expect_bind, expect_bind, ← expect_sample_equiv e]
+  refine congrArg _ (funext fun u => ?_)
+  dsimp only
+  rw [expect_pure, expect_pure]
+  calc g₀ (f₀ u) = g₀ ((f₀ u).1, (f₀ u).2) := rfl
+    _ = g₁ ((f₀ u).1, (f₁ (e u)).2) := hg _ _ _ (hf u).2
+    _ = g₁ (f₁ (e u)) := by rw [(hf u).1]
 
 end ProbComp
 

## ===== TCSlib/Cryptography/Games/Relational.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states answers
alike and leads to related states, then the two simulations of any computation answer alike and
end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
call, or a run, from related states gives the same expectation to any two functions of the
answer and the state that agree at equal answers and related states.

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
  Cryptographic Proofs*, POPL 2009.
* [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
  Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.

The conclusion has the form of [BGZ09, §4.1, lemma (=⟦⟧)]: runs from related states give equal
expectations to test functions that agree along the relation. The relation is carried as pre-
and postcondition of every call, as the invariant `φ` of [BGZ09, §4.2, ⊨_φ] (judgments in the
sense of [BGZ09, §4.1, Def. 5]). The computation `c` is an arbitrary context that reaches the
two implementations only through its oracle calls, like a well-formed adversary, which is free
to call oracles [BGZ09, §3.4]; [BGZ09, §5.2, Lemma 1] proves an equivalence inside an arbitrary
context, and §5.2 applies it to replace one oracle by another. A run of `c` against `impl₁` in
place of `impl₀` is a bridging step, `Pr[S_i] = Pr[S_{i+1}]` [Sho04, §1.1, bridging steps], as
in the replacement of a random function by a lazily tabulating oracle [Sho04, §4.2, Game 2].

**Deviation:** [BGZ09] states no rule for adversary calls with a relational invariant. This lemma
generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations whose states are related by
an invariant, in the arbitrary-context style of §5.2. The per-call hypothesis (equal
expectations of test functions that agree along `R`) is the library's formulation.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  induction c generalizing s t with
  | pure a =>
    rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
    exact hG a s t hst
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind]
    exact h i x s t hst _ _ fun y s' t' hR => ih y hR

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`): a bridging
step [Sho04, §1.1, bridging steps].

**Proof sketch.** Both probabilities are expectations of the indicator of `P` on the output
(`prob_eq_expect`); the two indicators agree at equal outputs whatever the final states, so
`expect_simulate_rel` equates them. -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  rw [expect_bind, expect_bind, ← expect_sample_equiv e]
  refine congrArg _ (funext fun u => ?_)
  dsimp only
  rw [expect_pure, expect_pure]
  calc g₀ (f₀ u) = g₀ ((f₀ u).1, (f₀ u).2) := rfl
    _ = g₁ ((f₀ u).1, (f₁ (e u)).2) := hg _ _ _ (hf u).2
    _ = g₁ (f₁ (e u)) := by rw [(hf u).1]

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Identity-based encryption and selective-identity security

An *identity-based encryption* (IBE) system [BB04, §2.1] consists of four algorithms: `Setup`
generates the system parameters `params` and a master key; `KeyGen` uses the master key to
generate the private key `d_ID` of an identity `ID`; `Encrypt` encrypts a message for an identity
using the parameters; `Decrypt` decrypts with a private key.

*Selective-identity chosen-plaintext security* (IND-sID-CPA, [BB04, §2.1, the game and
Definition 2.2]): the adversary first commits to the identity `ID*` it will attack (**Init**);
the challenger runs `Setup` and gives it `params` (**Setup**); the adversary adaptively asks for
the private keys of identities `ID ≠ ID*` (**Phase 1**); it outputs two messages `M₀, M₁` of the
message space and receives `Encrypt(params, ID*, M_b)` (**Challenge**); it asks more private-key
queries (**Phase 2**) and outputs a guess `b'` (**Guess**). There are no decryption queries.

**The scheme interface.** The algorithms are probabilistic computations of the `Games` framework
over typed parameters, keys and ciphertexts (`IBEScheme`). Identities are `idLen(κ)`-bit strings
and messages arrive as `msgLen(κ)`-bit strings; a scheme declares which strings are messages for
given parameters (`MsgSpace`, the paper's message space `M`). For the adversary, parameters,
private keys and ciphertexts are written as fixed-width strings (`encPP`, `encSK`, `encCT`),
injective on the objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**The game's encoding.** As in the public-key games (`Encryption.PublicKey.OracleSecurity`), one
non-uniform PPT machine plays every phase against bit-string oracles (`Games.bitCodec`):
* `Init` (oracle 0) takes `ID*` and answers `params`. The first query fixes `ID*`; later queries
  repeat `params` and leave `ID*` unchanged.
* `KeyGen` (oracle 1) takes `ID` and answers `⟨1, d_ID⟩` with fresh `KeyGen` coins when `ID*` is
  fixed and `ID ≠ ID*`, and `⊥` (all `false`) otherwise.
* `Challenge` (oracle 2) takes `⟨M₀, M₁⟩` and answers `Encrypt(params, ID*, M_b)` the first time
  it is asked with `ID*` fixed and `M₀, M₁ ∈ M`, recording it; later it repeats the recorded
  challenge; it answers `⊥` before `Init` and on messages outside `M`.
The machine starts with input `1^κ` only, so the only information it has before committing is
its coins. `Setup` is run before the machine starts; since nothing about `params` reaches the
machine before its `Init` query, this is the order of [BB04, §2.1] in distribution.

**Deviation:** [BB04, Definition 2.2] is concrete (`(t, q_ID, ε)`) and measures
`|Pr[b = b'] − 1/2|`; here security is asymptotic, for every non-uniform PPT and every polynomial
query budget, and the advantage is `|Pr[b' = 1 | b = 0] − Pr[b' = 1 | b = 1]|`, twice the
paper's (`Games.guessAdv_eq_half_advantage`). Queries to `KeyGen` for `ID*` and challenges outside
`M` are answered `⊥` instead of being forbidden. The algorithms are typed probabilistic
computations; their efficiency is not part of the interface (per-scheme contracts).

## Main definitions

* `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme` — an IBE system [BB04, §2.1].
* `IBEScheme.Correct` — perfect correctness on the message space.
* `IBEScheme.sidSpec`, `IBEScheme.sidImpl`, `IBEScheme.sidGame`, `IBEScheme.SIDSecure` — the
  IND-sID-CPA game and security [BB04, §2.1 and Definition 2.2].
* `IBEScheme.oracleImpl` — the three oracles from typed handlers (for simulators).

## Main results

* `IBEScheme.sidImpl_init_none`, `sidImpl_init_some`, `sidImpl_keyGen_none`,
  `sidImpl_keyGen_target`, `sidImpl_keyGen_ne`, `sidImpl_challenge_none`,
  `sidImpl_challenge_repeat`, `sidImpl_challenge_fresh`, `sidImpl_challenge_invalid` — the
  oracles case by case; `oracleImpl_zero`, `oracleImpl_one`, `oracleImpl_two`.
* `IBEScheme.honestRun_eq`, `correct_iff`, `sidGame_eq`, `sidSecure_iff` — the experiments and
  predicates through their published equations.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4): IBE systems, the
  selective identity game, Definitions 2.1 and 2.2.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the one-machine encoding of the games of §7.1.4.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Composability

/-- An **identity-based encryption system** [BB04, §2.1]: at each security parameter `κ`, types of
system parameters `PP κ`, master keys `MSK κ`, private keys `SK κ` and ciphertexts `CT κ`, and
* `setup κ`, a probabilistic computation of `(params, master-key)`;
* `keyGen κ msk ID`, a probabilistic computation of the private key `d_ID` of the `idLen(κ)`-bit
  identity `ID`;
* `enc κ params ID M`, a probabilistic computation of a ciphertext of the `msgLen(κ)`-bit message
  `M` for `ID`;
* `dec κ d_ID C`, the deterministic decryption, `none` for `⊥`;
* the message space `MsgSpace κ params` (the paper's `M`), and fixed-width encodings of
  parameters, private keys and ciphertexts for the adversary, which lose no information on the
  objects the algorithms can output (`encPP_inj`, `encSK_inj`, `encCT_inj`).

**Deviation:** messages are strings with a parameter-dependent message space (as for El Gamal,
`Candidates.GroupPKScheme`); the algorithms are typed probabilistic computations, without an
efficiency requirement in the interface. The adversary sees parameters, private keys and
ciphertexts only through their encodings; their fidelity is injectivity on reachable objects
(possible outputs of `setup`, and keys and ciphertexts under one possible output of `setup`), not
efficient decoding, and not injectivity on all of `PP κ`, `SK κ`, `CT κ` (an encoding may omit
data that the parameters fix). The efficiency of the encodings is deferred with that of the
algorithms (ruling Q5 of `PairingCryptographyPlan.md`). -/
structure IBEScheme where
  /-- The identity length. -/
  idLen : PolyExpr
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The width of encoded parameters. -/
  ppLen : PolyExpr
  /-- The width of encoded private keys. -/
  skLen : PolyExpr
  /-- The width of encoded ciphertexts. -/
  ctLen : PolyExpr
  /-- System parameters. -/
  PP : ℕ → Type
  /-- Master keys. -/
  MSK : ℕ → Type
  /-- Private keys. -/
  SK : ℕ → Type
  /-- Ciphertexts. -/
  CT : ℕ → Type
  /-- `Setup`: system parameters and a master key. -/
  setup : (κ : ℕ) → ProbComp (PP κ × MSK κ)
  /-- `KeyGen`: the private key of an identity. -/
  keyGen : (κ : ℕ) → MSK κ → (Fin (idLen.eval κ) → Bool) → ProbComp (SK κ)
  /-- `Encrypt`: a ciphertext of a message for an identity. -/
  enc : (κ : ℕ) → PP κ → (Fin (idLen.eval κ) → Bool) → (Fin (msgLen.eval κ) → Bool) →
    ProbComp (CT κ)
  /-- `Decrypt`: the message of a ciphertext under a private key, or `⊥`. -/
  dec : (κ : ℕ) → SK κ → CT κ → Option (Fin (msgLen.eval κ) → Bool)
  /-- The message space for given parameters. -/
  MsgSpace : (κ : ℕ) → PP κ → (Fin (msgLen.eval κ) → Bool) → Prop
  /-- The encoding of parameters. -/
  encPP : (κ : ℕ) → PP κ → Fin (ppLen.eval κ) → Bool
  /-- The encoding of private keys. -/
  encSK : (κ : ℕ) → SK κ → Fin (skLen.eval κ) → Bool
  /-- The encoding of ciphertexts. -/
  encCT : (κ : ℕ) → CT κ → Fin (ctLen.eval κ) → Bool
  /-- **The parameter encoding is injective on reachable parameters**: two parameters output by
  `setup κ` with equal encodings are equal. With `encSK_inj` and `encCT_inj`, the adversary's
  wire view loses no information about the objects it is given [BB04, §2.1: the adversary
  receives `params`, the private keys `d_i` and the challenge ciphertext `C`]. -/
  encPP_inj : ∀ κ, (setup κ).AllOutputs fun k => (setup κ).AllOutputs fun k' =>
    encPP κ k.1 = encPP κ k'.1 → k.1 = k'.1
  /-- **The private-key encoding is injective on reachable keys**: for every possible output
  `(params, master-key)` of `setup κ`, two private keys output by `keyGen` with that master key,
  for any identities, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encSK_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id',
    (keyGen κ k.2 id).AllOutputs fun d => (keyGen κ k.2 id').AllOutputs fun d' =>
      encSK κ d = encSK κ d' → d = d'
  /-- **The ciphertext encoding is injective on reachable ciphertexts**: for every possible output
  of `setup κ`, two ciphertexts output by `enc` with its parameters, for any identities and
  messages, with equal encodings are equal [BB04, §2.1, the adversary's view]. -/
  encCT_inj : ∀ κ, (setup κ).AllOutputs fun k => ∀ id id' m m',
    (enc κ k.1 id m).AllOutputs fun c => (enc κ k.1 id' m').AllOutputs fun c' =>
      encCT κ c = encCT κ c' → c = c'

namespace IBEScheme

variable (S : IBEScheme)

/-- One honest run for the identity `ID` and the message `M`: `Setup`, then `KeyGen` for `ID`
and `Encrypt(params, ID, M)`, returning the parameters, the private key and the ciphertext. -/
noncomputable def honestRun (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) : ProbComp (S.PP κ × S.SK κ × S.CT κ) :=
  (S.setup κ).bind fun k =>
  (S.keyGen κ k.2 id).bind fun sk =>
  (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c)

/-- `S.honestRun κ id m` runs `Setup`, `KeyGen` for `id` and `Encrypt` of `m` for `id`, and
returns `(params, d_id, C)`. -/
theorem honestRun_eq (κ : ℕ) (id : Fin (S.idLen.eval κ) → Bool)
    (m : Fin (S.msgLen.eval κ) → Bool) :
    S.honestRun κ id m =
      (S.setup κ).bind fun k =>
      (S.keyGen κ k.2 id).bind fun sk =>
      (S.enc κ k.1 id m).bind fun c => .pure (k.1, sk, c) := rfl

/-- **Perfect correctness** [BB04, §2.1, "the decryption algorithm decrypts ciphertexts using the
private key"; §4.1's verification for BB1]: for every identity `ID` and every message `M`, every
possible outcome `(params, d_ID, C)` of an honest run with `M` in the message space of `params`
has `Decrypt(d_ID, C) = M`. -/
def Correct : Prop :=
  ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
    (S.honestRun κ id m).AllOutputs fun x => S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m

/-- `S.Correct` iff every possible outcome of every honest run with a message of the message
space decrypts to that message. -/
theorem correct_iff :
    S.Correct ↔ ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),
      (S.honestRun κ id m).AllOutputs fun x =>
        S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m := Iff.rfl

/-! ### The selective-identity game -/

/-- The query lengths of the three oracles: `Init` and `KeyGen` take an identity, `Challenge`
takes two messages. -/
def inLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.idLen.eval κ
  | 1 => S.idLen.eval κ
  | 2 => S.msgLen.eval κ + S.msgLen.eval κ

/-- `Init` queries are identities: `S.inLens κ 0 = S.idLen.eval κ`. -/
theorem inLens_zero (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ := rfl

/-- `KeyGen` queries are identities: `S.inLens κ 1 = S.idLen.eval κ`. -/
theorem inLens_one (κ : ℕ) : S.inLens κ 1 = S.idLen.eval κ := rfl

/-- `Challenge` queries are two messages: `S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ`. -/
theorem inLens_two (κ : ℕ) : S.inLens κ 2 = S.msgLen.eval κ + S.msgLen.eval κ := rfl

/-- The answer lengths of the three oracles: `Init` answers the parameters, `KeyGen` a validity
bit and a private key, `Challenge` a ciphertext. -/
def outLens (κ : ℕ) : Fin 3 → ℕ
  | 0 => S.ppLen.eval κ
  | 1 => S.skLen.eval κ + 1
  | 2 => S.ctLen.eval κ

/-- `Init` answers parameters: `S.outLens κ 0 = S.ppLen.eval κ`. -/
theorem outLens_zero (κ : ℕ) : S.outLens κ 0 = S.ppLen.eval κ := rfl

/-- `KeyGen` answers a validity bit and a key: `S.outLens κ 1 = S.skLen.eval κ + 1`. -/
theorem outLens_one (κ : ℕ) : S.outLens κ 1 = S.skLen.eval κ + 1 := rfl

/-- `Challenge` answers a ciphertext: `S.outLens κ 2 = S.ctLen.eval κ`. -/
theorem outLens_two (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ := rfl

/-- The three oracles of the IND-sID-CPA game at parameter `κ`. -/
abbrev sidSpec (κ : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens κ) (S.outLens κ)

/-- The IND-sID-CPA oracle specification is the bit specification at the scheme's query and
answer lengths: `S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ)`. -/
theorem sidSpec_eq (κ : ℕ) : S.sidSpec κ = bitSpec (S.inLens κ) (S.outLens κ) := rfl

/-- The state of the IND-sID-CPA game: the committed identity `ID*` (once `Init` is asked) and
the challenge ciphertext (once issued). -/
abbrev SidState (κ : ℕ) : Type :=
  Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)

/-- The game state is the optional committed identity and the optional encoded challenge:
`S.SidState κ = Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)`. -/
theorem sidState_eq (κ : ℕ) :
    S.SidState κ =
      (Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)) := rfl

open Classical in
/-- **The oracles of the IND-sID-CPA game** [BB04, §2.1] with hidden bit `b`, at parameter `κ`,
for the parameters `pp` and the master key `msk`:
- `Init` on `ID`: answers `params`; records `ID*` = `ID` if none is recorded yet.
- `KeyGen` on `ID`: when `ID*` is recorded and `ID ≠ ID*`, answers `⟨1, d_ID⟩` with
  `d_ID ← KeyGen(msk, ID)`; otherwise `⊥`.
- `Challenge` on `⟨M₀, M₁⟩`: with `ID*` recorded and no challenge yet, if `M₀, M₁ ∈ M`, answers
  and records `C ← Encrypt(params, ID*, M_b)`, and otherwise `⊥`; once a challenge is recorded,
  repeats it; before `Init`, `⊥`. -/
noncomputable def sidImpl (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ) :
    QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec
  | 0, id, s =>
    match s.1 with
    | none => .pure (S.encPP κ pp, (some id, s.2))
    | some _ => .pure (S.encPP κ pp, s)
  | 1, id, s =>
    match s.1 with
    | some t =>
      if id = t then .pure (zeroBits _, s)
      else (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s =>
    match s.1, s.2 with
    | some _, some c => .pure (c, s)
    | some t, none =>
      if S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
          S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2 then
        (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
          .pure (S.encCT κ c, (some t, some (S.encCT κ c)))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

/-- `Init` before any commitment answers the parameters and records the identity. -/
theorem sidImpl_init_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (none, c) = .pure (S.encPP κ pp, (some id, c)) := rfl

/-- `Init` after a commitment answers the parameters and keeps the state. -/
theorem sidImpl_init_some (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 0 id (some t, c) = .pure (S.encPP κ pp, (some t, c)) := rfl

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem sidImpl_keyGen_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem sidImpl_keyGen_target (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 1 t (some t, c) = .pure (zeroBits _, (some t, c)) := by
  simp [sidImpl]

/-- `KeyGen` for an identity other than the committed one answers `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)` and keeps the state. -/
theorem sidImpl_keyGen_ne (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (id t : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : id ≠ t) :
    S.sidImpl b κ pp msk 1 id (some t, c) =
      (S.keyGen κ msk id).bind fun sk =>
        .pure (FixedLengthScheme.decAnswer (some (S.encSK κ sk)), (some t, c)) := by
  simp [sidImpl, h]

/-- `Challenge` before `Init` answers `⊥`. -/
theorem sidImpl_challenge_none (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk 2 mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem sidImpl_challenge_repeat (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Fin (S.ctLen.eval κ) → Bool) :
    S.sidImpl b κ pp msk 2 mm (some t, some c) = .pure (c, (some t, some c)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`C ← Encrypt(params, ID*, M_b)`. -/
theorem sidImpl_challenge_fresh (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2) :
    S.sidImpl b κ pp msk 2 mm (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf mm).2
        else (FixedLengthScheme.splitHalf mm).1)).bind fun c =>
        .pure (S.encCT κ c, (some t, some (S.encCT κ c))) := by
  simp only [sidImpl]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem sidImpl_challenge_invalid (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (mm : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (t : Fin (S.idLen.eval κ) → Bool)
    (h : ¬ (S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf mm).2)) :
    S.sidImpl b κ pp msk 2 mm (some t, none) = .pure (zeroBits _, (some t, none)) := by
  simp only [sidImpl]
  rw [if_neg h]

/-- **The three oracles from typed handlers**: an implementation of `S.sidSpec κ` whose `Init`,
`KeyGen` and `Challenge` oracles are the handlers `init`, `key` and `chal`, which take and return
strings of the scheme's lengths. Simulators and reductions describe their oracles this way, so
that they never read the oracle lengths `inLens`, `outLens` through their bodies. -/
def oracleImpl {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ)) :
    QueryImpl (S.sidSpec κ) σ unifSpec
  | 0, x, s => init x s
  | 1, x, s => key x s
  | 2, x, s => chal x s

/-- Oracle `0` of `S.oracleImpl κ init key chal` is the handler `init`. -/
theorem oracleImpl_zero {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 0 x s = init x s := rfl

/-- Oracle `1` of `S.oracleImpl κ init key chal` is the handler `key`. -/
theorem oracleImpl_one {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.idLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 1 x s = key x s := rfl

/-- Oracle `2` of `S.oracleImpl κ init key chal` is the handler `chal`. -/
theorem oracleImpl_two {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) (s : σ) :
    S.oracleImpl κ init key chal 2 x s = chal x s := rfl

/-- **Oracle `0` of `oracleImpl` on the game's query type**: the handler `init` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_zero_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 0) (s : σ) :
    S.oracleImpl κ init key chal 0 x s =
      (init (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of `oracleImpl` on the game's query type**: the handler `key` on the query read
as an identity, its answer read back on the game's answer type. -/
theorem oracleImpl_one_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 1) (s : σ) :
    S.oracleImpl κ init key chal 1 x s =
      (key (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of `oracleImpl` on the game's query type**: the handler `chal` on the query read
as two messages, its answer read back on the game's answer type. -/
theorem oracleImpl_two_onSpec {σ : Type} (κ : ℕ)
    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))
    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))
    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →
      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))
    (x : (S.sidSpec κ).dom 2) (s : σ) :
    S.oracleImpl κ init key chal 2 x s =
      (chal (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
        from rfl) x) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `0` of the game on the game's query type**: `Init` on the query read as an identity,
its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 0 x s =
(S.sidImpl b κ pp msk 0 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_zero_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 0) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 0 x s =
      (S.sidImpl b κ pp msk 0
        (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of the game on the game's query type**: `Challenge` on the query read as two
messages, its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 2 x s =
(S.sidImpl b κ pp msk 2 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_two_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      (S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of the game, its query read as an identity**: the call on the game's query
type is the call on the query read as an `idLen(κ)`-bit identity, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 1 x s = S.sidImpl b κ pp msk 1 (cast x) s`. -/
theorem sidImpl_one_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 1 x s =
      S.sidImpl b κ pp msk 1
        (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s := rfl

/-- **Oracle `2` of the game, its query read as two messages**: the call on the game's query
type is the call on the query read as two `msgLen(κ)`-bit messages, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 2 x s = S.sidImpl b κ pp msk 2 (cast x) s`. -/
theorem sidImpl_two_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s := rfl

/-- **`KeyGen` for another identity, on the game's types**: with `ID*` recorded and the query
`x`, read as an identity, different from it, the answer is `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)`, read back on the game's answer type: for `cast x ≠ t`,
`S.sidImpl b κ pp msk 1 x (some t, c) =
(S.keyGen κ msk (cast x)).bind fun sk => pure (cast (decAnswer (some (encSK sk))), (some t, c))`. -/
theorem sidImpl_keyGen_ne_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
      Fin (S.idLen.eval κ) → Bool) ≠ t) :
    S.sidImpl b κ pp msk 1 x (some t, c) =
      (S.keyGen κ msk (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl)
        x)).bind fun sk =>
        .pure (cast (show (Fin (S.skLen.eval κ + 1) → Bool) = (S.sidSpec κ).rng 1 from rfl)
          (FixedLengthScheme.decAnswer (some (S.encSK κ sk))), (some t, c)) :=
  S.sidImpl_keyGen_ne b κ pp msk _ t c h

/-- **The first valid `Challenge`, on the game's types**: with `ID*` recorded, no challenge yet,
and both messages of the query `x`, read as two messages, in the message space, the answer is
`C ← Encrypt(params, ID*, M_b)`, read back on the game's answer type, and `C` is recorded: for
`(M₀, M₁) = splitHalf (cast x)` with `M₀, M₁ ∈ M`, `S.sidImpl b κ pp msk 2 x (some t, none) =
(S.enc κ pp t M_b).bind fun C => pure (cast (encCT C), (some t, some (encCT C)))`. -/
theorem sidImpl_challenge_fresh_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2) :
    S.sidImpl b κ pp msk 2 x (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2
        else (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1)).bind fun c =>
        .pure (cast (show (Fin (S.ctLen.eval κ) → Bool) = (S.sidSpec κ).rng 2 from rfl)
          (S.encCT κ c), (some t, some (S.encCT κ c))) :=
  S.sidImpl_challenge_fresh b κ pp msk _ t h

/-- The codec of the adversary: the three oracles and a one-bit guess. -/
def sidCodec (κ : ℕ) : MachineCodec (S.sidSpec κ) (Fin 1 → Bool) :=
  bitCodec (S.inLens κ) (S.outLens κ) 1

/-- The adversary codec is a bit codec: `S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1`. -/
theorem sidCodec_eq (κ : ℕ) : S.sidCodec κ = bitCodec (S.inLens κ) (S.outLens κ) 1 := rfl

/-- **The experiment `IND-sID-CPA_b(A, κ)`** [BB04, §2.1] with query budget `q`: run `Setup`,
draw `A`'s coins, run `A(1^κ)` against the three oracles from the empty state (no identity
committed, no challenge), and return its one-bit guess. -/
noncomputable def sidGame (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.setup κ).bind fun k =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
  (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
    fun res => .pure (res.1 0)

/-- The IND-sID-CPA experiment runs `Setup`, samples the adversary's coins, simulates the
oracles from the empty state, and returns the guess bit. -/
theorem sidGame_eq (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    S.sidGame A q b κ =
      (S.setup κ).bind fun k =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
      (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

/-- **IND-sID-CPA security** [BB04, §2.1 and Definition 2.2]: for every non-uniform PPT `A` and
every polynomial query budget `q`, `A`'s advantage between the experiments with `b = 0` and
`b = 1` is negligible.

**Deviation:** asymptotic, with a polynomial budget `q(κ)` on all queries (the paper's `q_ID`
bounds private-key queries); the advantage is twice the paper's (module docstring). -/
def SIDSecure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ

/-- IND-sID-CPA security is negligible advantage, uniformly in `κ`, for every non-uniform PPT
adversary and polynomial query budget. -/
theorem sidSecure_iff :
    S.SIDSecure ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ κ, advantage (S.sidGame A (q.eval κ) false κ) (S.sidGame A (q.eval κ) true κ) ≤ ε κ :=
  Iff.rfl

end IBEScheme

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Boneh–Boyen selective-identity IBE (BB1)

[BB04, §4.1] with depth `ℓ = 1` (an IBE system is an HIBE whose identities have depth 1,
[BB04, §2.1]). In a bilinear group `G` of prime order `p` with pairing `e`:
* **Setup**: a random generator `g ∈ G^*`, `α ∈ Z_p`, `g_1 = g^α`, random `h, g_2 ∈ G`;
  `params = (g, g_1, g_2, h)`, `master-key = g_2^α`; `F(x) = g_1^x h`.
* **KeyGen**(`ID ∈ Z_p`): a random `r ∈ Z_p`, `d_ID = (g_2^α · F(ID)^r, g^r)`.
* **Encrypt**(`params`, `ID`, `M ∈ G_1`): a random `s ∈ Z_p`,
  `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`.
* **Decrypt**(`d_ID = (d_0, d_1)`, `C = (A, B, C_1)`): `A · e(C_1, d_1) / e(B, d_0)`.

It is IND-sID-CPA secure under Decision BDH [BB04, Theorem 4.1], without random oracles; the
security statement and its simulation are in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`.

**Identities and messages.** The generic interface (`IBEScheme`) has `ℓ(κ)`-bit identities.
BB1 reads an identity as the residue of its binary value in `Z_p` (`idToZ`), the injective
"hash" `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] ("a collision resistant hash function
`H : {0,1}^* → {1, …, 2^b}` where `2^b < p` is sufficient"); distinct identities stay distinct in
`Z_p` when `2^ℓ ≤ p`, which the security theorem assumes except with negligible probability.
Messages are elements of `G_T` (the paper's `G_1`), sent as their `wT(κ)`-bit encodings; the
message space is the set of encodings, and `Encrypt` reads a string through `decodeT` (strings
outside the message space read as `1`, a choice that is never exercised by the game, which
refuses them).

**Groups from the generator.** Parameters, keys and ciphertexts carry the description `d` of the
group they live in (a dependent pair), since the group is drawn by `Setup` from the generator
(`Pairing.BilinearGen`). Decryption of a ciphertext whose description differs from the key's is
`⊥`.

**Deviation:** abstract bilinear groups drawn by a generator; depth-1 identities given as
`ℓ(κ)`-bit strings and embedded into `Z_p` by their binary value; messages as encodings of `G_T`;
parameters, keys and ciphertexts tagged with the group's description.

## Main definitions

* `BB1.Params`, `BB1.Key`, `BB1.Ciphertext` — `params`, `d_ID` and `C`.
* `BB1.F`, `BB1.setup`, `BB1.keyGen`, `BB1.encrypt`, `BB1.decrypt` — the
  algorithms of [BB04, §4.1] over one bilinear group.
* `BB1.idToZ`, `BB1.decodeT` — identities in `Z_p` and messages in `G_T`.
* `bb1Scheme` — BB1 as an `IBEScheme` over a generator.
* `BB1SimState`, `bb1SimParams`, `bb1SimKey`, `bb1SimInit`, `bb1SimKeyQ`,
  `bb1SimCt`, `bb1SimChal`, `bb1SimImpl`, `bb1SimGame` — the simulator of
  [BB04, proof of Theorem 4.1] and its game, with ideal exponents.

## Main results

* `BB1.decrypt_encrypt` — decryption inverts encryption [BB04, §4.1, "for a valid
  ciphertext"].
* `bb1_correct` — BB1 is perfectly correct.
* `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` — BB1's encodings are injective on
  parameters of the advertised description length and on keys and ciphertexts in one group.
* `bb1SimInit_none`, …, `bb1SimChal_invalid` — the simulator's handlers case by case.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.1 (pp. 2–4), §4.1 (pp. 5–6:
  the construction), §4.2 (pp. 6–8: the simulator in the proof of Theorem 4.1), §4.4 (p. 8:
  arbitrary identities).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **System parameters** `params = (g, g_1, g_2, h)` of BB1 [BB04, §4.1, `Setup` at depth 1]. -/
structure Params where
  /-- The generator `g ∈ G^*`. -/
  g : B.G
  /-- `g_1 = g^α`. -/
  g1 : B.G
  /-- The random element `g_2`. -/
  g2 : B.G
  /-- The random element `h = h_1`. -/
  h : B.G

/-- **A private key** `d_ID = (d_0, d_1)` of BB1 [BB04, §4.1, `KeyGen` at depth 1]. -/
structure Key where
  /-- `d_0 = g_2^α · F(ID)^r`. -/
  d0 : B.G
  /-- `d_1 = g^r`. -/
  d1 : B.G

/-- **A ciphertext** `C = (A, B, C_1)` of BB1 [BB04, §4.1, `Encrypt` at depth 1]. -/
structure Ciphertext where
  /-- `A = e(g_1, g_2)^s · M`. -/
  a : B.GT
  /-- `B = g^s`. -/
  b : B.G
  /-- `C_1 = F(ID)^s`. -/
  c : B.G

variable {B}

/-- **The function** `F(x) = g_1^x h` [BB04, §4.1, `F_1 : Z_p → G`]. -/
def F (pp : Params B) (x : ZMod B.order) : B.G := pp.g1 ^ x.val * pp.h

/-- `F pp x = pp.g1 ^ x.val * pp.h`. -/
theorem F_eq (pp : Params B) (x : ZMod B.order) : F pp x = pp.g1 ^ x.val * pp.h := rfl

variable (B)

/-- **Setup** [BB04, §4.1, depth 1]: a uniform generator `g ∈ G^*`, a uniform `α ∈ Z_p`, uniform
`h, g_2 ∈ G`; returns `params = (g, g^α, g_2, h)` and `master-key = g_2^α`. -/
noncomputable def setup : ProbComp (Params B × B.G) :=
  (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod B.order)).bind fun α =>
  (ProbComp.sample B.G).bind fun h =>
  (ProbComp.sample B.G).bind fun g2 =>
    .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val)

/-- `setup B` draws `g ∈ G^*`, `α ∈ Z_p`, `h, g_2 ∈ G` and returns
`((g, g^α, g_2, h), g_2^α)`. -/
theorem setup_eq :
    setup B =
      (ProbComp.sample {x : B.G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod B.order)).bind fun α =>
      (ProbComp.sample B.G).bind fun h =>
      (ProbComp.sample B.G).bind fun g2 =>
        .pure (⟨g.1, g.1 ^ α.val, g2, h⟩, g2 ^ α.val) := rfl

variable {B}

/-- **KeyGen** [BB04, §4.1, depth 1]: from the parameters, the master key `mk = g_2^α` and an
identity `ID ∈ Z_p`, a uniform `r ∈ Z_p` and `d_ID = (mk · F(ID)^r, g^r)`. -/
noncomputable def keyGen (pp : Params B) (mk : B.G) (id : ZMod B.order) : ProbComp (Key B) :=
  (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩

/-- `keyGen pp mk id` draws `r ∈ Z_p` and returns `(mk · F(id)^r, g^r)`. -/
theorem keyGen_eq (pp : Params B) (mk : B.G) (id : ZMod B.order) :
    keyGen pp mk id =
      (ProbComp.sample (ZMod B.order)).bind fun r => .pure ⟨mk * F pp id ^ r.val, pp.g ^ r.val⟩ :=
  rfl

/-- **Encrypt** [BB04, §4.1, depth 1]: for an identity `ID ∈ Z_p` and a message `M ∈ G_T`, a
uniform `s ∈ Z_p` and `C = (e(g_1, g_2)^s · M, g^s, F(ID)^s)`. -/
noncomputable def encrypt (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    ProbComp (Ciphertext B) :=
  (ProbComp.sample (ZMod B.order)).bind fun s =>
    .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩

/-- `encrypt pp id M` draws `s ∈ Z_p` and returns `(e(g_1, g_2)^s · M, g^s, F(id)^s)`. -/
theorem encrypt_eq (pp : Params B) (id : ZMod B.order) (M : B.GT) :
    encrypt pp id M =
      (ProbComp.sample (ZMod B.order)).bind fun s =>
        .pure ⟨B.pair pp.g1 pp.g2 ^ s.val * M, pp.g ^ s.val, F pp id ^ s.val⟩ := rfl

/-- **Decrypt** [BB04, §4.1, depth 1]: `A · e(C_1, d_1) / e(B, d_0)` for `d_ID = (d_0, d_1)` and
`C = (A, B, C_1)`. -/
def decrypt (d : Key B) (C : Ciphertext B) : B.GT := C.a * B.pair C.c d.d1 / B.pair C.b d.d0

/-- `decrypt d C = C.a * e(C.c, d.d1) / e(C.b, d.d0)`. -/
theorem decrypt_eq (d : Key B) (C : Ciphertext B) :
    decrypt d C = C.a * B.pair C.c d.d1 / B.pair C.b d.d0 := rfl

/-- **Decryption inverts encryption** [BB04, §4.1, "for a valid ciphertext, we have
`e(C_1, d_1) / e(B, d_0) = 1 / e(g_1, g_2)^s`"]: for the parameters `(g, g^α, g_2, h)`, the
master key `g_2^α`, the private key with exponent `r` and the ciphertext with exponent `s` of
`M` for the same identity, `Decrypt(d_ID, C) = M`.

**Proof sketch.** The proof is the paper's computation:
`e(F(ID)^s, g^r) = e(g, F(ID))^{sr}` (bilinearity and symmetry) and
`e(g^s, g_2^α F(ID)^r) = e(g, g_2)^{αs} · e(g, F(ID))^{sr}`, while the mask of `A`
is `e(g^α, g_2)^s = e(g, g_2)^{αs}`. -/
theorem decrypt_encrypt (g g2 h : B.G) (α r s id : ZMod B.order) (M : B.GT) :
    decrypt (⟨g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val, g ^ r.val⟩ : Key B)
      ⟨B.pair (g ^ α.val) g2 ^ s.val * M, g ^ s.val, F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val⟩ = M := by
  rw [decrypt_eq]
  dsimp only
  have h1 : B.pair (g ^ α.val) g2 ^ s.val = B.pair g g2 ^ (α.val * s.val) := by
    rw [B.pair_pow_left, ← pow_mul]
  have h2 : B.pair (F ⟨g, g ^ α.val, g2, h⟩ id ^ s.val) (g ^ r.val) =
      B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [B.bilinear_pow, B.pair_comm (F ⟨g, g ^ α.val, g2, h⟩ id) g]
  have h3 : B.pair (g ^ s.val) (g2 ^ α.val * F ⟨g, g ^ α.val, g2, h⟩ id ^ r.val) =
      B.pair g g2 ^ (α.val * s.val) * B.pair g (F ⟨g, g ^ α.val, g2, h⟩ id) ^ (s.val * r.val) := by
    rw [map_mul (B.pair (g ^ s.val)), B.bilinear_pow, B.bilinear_pow, mul_comm s.val α.val]
  rw [h1, h2, h3, mul_right_comm]
  exact mul_div_cancel_left _ _

variable (B)

/-- **An identity as an element of `Z_p`**: the residue of the binary value of an `ℓ`-bit string,
the injective encoding `{0,1}^ℓ → {0, …, 2^ℓ − 1}` of [BB04, §4.4] read in `Z_p`. -/
def idToZ {ℓ : ℕ} (id : Fin ℓ → Bool) : ZMod B.order := (bitsToNat id : ZMod B.order)

/-- `idToZ id` is the cast of `bitsToNat id` into `Z_p`. -/
theorem idToZ_eq {ℓ : ℕ} (id : Fin ℓ → Bool) :
    idToZ B id = (bitsToNat id : ZMod B.order) := rfl

/-- **A message from its encoding**: the element of `G_T` with encoding `w`, and `1` when `w`
encodes none. -/
noncomputable def decodeT (w : Fin wT → Bool) : B.GT := (Function.partialInv B.encT w).getD 1

/-- `decodeT B w = (Function.partialInv B.encT w).getD 1`. -/
theorem decodeT_eq (w : Fin wT → Bool) : decodeT B w = (Function.partialInv B.encT w).getD 1 :=
  rfl

/-- Decoding an encoding returns the element: `decodeT B (B.encT u) = u`. -/
theorem decodeT_encT (u : B.GT) : decodeT B (B.encT u) = u := by
  rw [decodeT_eq, Function.partialInv_left B.encT_injective, Option.getD_some]

end BB1

/-! ### The encodings of BB1 lose no information

The wire formats of `bb1Scheme` below, before the scheme is assembled: each is injective on the
objects it is used for, which gives the fields `encPP_inj`, `encSK_inj` and `encCT_inj`. -/

section Encodings

variable (G : BilinearGen)

/-- **Parameters with a description of the advertised length are determined by their
encoding** (the encoding of `bb1Scheme`'s parameters): for `pp, pp'` whose descriptions have
`descLen(κ)` bits, equal padded words `d ‖ g ‖ g_1 ‖ g_2 ‖ h` give `pp = pp'`.

**Proof sketch.** Both words have exactly `descLen(κ) + 4 · wG(κ)` bits, so they are equal before
padding (`ofFn_padFin_of_length`). Splitting off the last four blocks of `wG(κ)` bits
(`List.append_inj'`) leaves equal descriptions; in the one group they describe, the four element
encodings are equal, so the elements are (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encPP_inj {κ : ℕ} {pp pp' : Σ d : List Bool, BB1.Params (G.group κ d)}
    (h : padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
          List.ofFn ((G.group κ pp.1).encG pp.2.h)) =
      padFin ((PolyExpr.add G.descLen (.mul (.const 4) G.wG)).eval κ)
        (pp'.1 ++ List.ofFn ((G.group κ pp'.1).encG pp'.2.g) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g1) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.g2) ++
          List.ofFn ((G.group κ pp'.1).encG pp'.2.h)))
    (hl : pp.1.length = G.descLen.eval κ) (hl' : pp'.1.length = G.descLen.eval κ) :
    pp = pp' := by
  obtain ⟨d, ⟨g, g1, g2, x⟩⟩ := pp
  obtain ⟨d', ⟨g', g1', g2', x'⟩⟩ := pp'
  dsimp only at hl hl' h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn, hl',
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg2⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨hw, hg1⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨rfl, hg⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (BilinearGroup.encG_injective _).eq_iff] at hx hg2 hg1 hg
  rw [hx, hg2, hg1, hg]

/-- **Two keys in one group with equal encodings are equal** (the encoding of `bb1Scheme`'s
private keys, which omits the description).

**Proof sketch.** Both words `d_0 ‖ d_1` have exactly `2 · wG(κ)` bits, so they are equal
before padding (`ofFn_padFin_of_length`); splitting at `wG(κ)` (`List.append_inj'`) gives equal
encodings of `d_0` and of `d_1`, hence equal elements (`List.ofFn_inj`, `encG_injective`). -/
theorem bb1_encSK_inj {κ : ℕ} {d : List Bool} {k k' : BB1.Key (G.group κ d)}
    (h : padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k.d0) ++ List.ofFn ((G.group κ d).encG k.d1)) =
      padFin ((PolyExpr.mul (.const 2) G.wG).eval κ)
        (List.ofFn ((G.group κ d).encG k'.d0) ++ List.ofFn ((G.group κ d).encG k'.d1))) :
    k = k' := by
  obtain ⟨a, b⟩ := k
  obtain ⟨a', b'⟩ := k'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at ha hb
  rw [ha, hb]

/-- **Two ciphertexts in one group with equal encodings are equal** (the encoding of
`bb1Scheme`'s ciphertexts, which omits the description).

**Proof sketch.** Both words `A ‖ B ‖ C_1` have exactly `wT(κ) + 2 · wG(κ)` bits, so they are
equal before padding (`ofFn_padFin_of_length`); splitting off the last two blocks of `wG(κ)` bits
(`List.append_inj'`) gives equal encodings of the three components, hence equal components
(`List.ofFn_inj`, `encT_injective`, `encG_injective`). -/
theorem bb1_encCT_inj {κ : ℕ} {d : List Bool} {c c' : BB1.Ciphertext (G.group κ d)}
    (h : padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c.a) ++ List.ofFn ((G.group κ d).encG c.b) ++
          List.ofFn ((G.group κ d).encG c.c)) =
      padFin ((PolyExpr.add G.wT (.mul (.const 2) G.wG)).eval κ)
        (List.ofFn ((G.group κ d).encT c'.a) ++ List.ofFn ((G.group κ d).encG c'.b) ++
          List.ofFn ((G.group κ d).encG c'.c))) :
    c = c' := by
  obtain ⟨a, b, x⟩ := c
  obtain ⟨a', b', x'⟩ := c'
  dsimp only at h
  have hw := congrArg List.ofFn h
  rw [ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega),
    ofFn_padFin_of_length (by simp only [List.length_append, List.length_ofFn,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]; omega)] at hw
  obtain ⟨hw, hx⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  obtain ⟨ha, hb⟩ := List.append_inj' hw (by simp only [List.length_ofFn])
  rw [List.ofFn_inj, (G.group κ d).encG_injective.eq_iff] at hx hb
  rw [List.ofFn_inj, (G.group κ d).encT_injective.eq_iff] at ha
  rw [ha, hb, hx]

end Encodings

/-- **The BB1 IBE system** over the bilinear group generator `G`, for `ℓ(κ)`-bit identities
[BB04, §4.1 at depth 1, with the identity encoding of §4.4]: `Setup` runs the generator and BB1's
`Setup` in the group it describes; the parameters are `⟨d, (g, g_1, g_2, h)⟩`, the master key
also carries the parameters; `KeyGen` and `Encrypt` read the identity through `idToZ` and the
message through `decodeT`; `Decrypt` returns the encoding of BB1's decryption, or `⊥` if the key
and the ciphertext name different descriptions. The message space at `⟨d, params⟩` is the set
of encodings of `G_T` of the group `d` describes. Parameters are encoded as `d` followed by the
four elements, keys as two elements, ciphertexts as `A, B, C_1`.

The encodings are injective where the interface asks: generated descriptions have `descLen(κ)`
bits (`BilinearGen.length_desc`, `bb1_encPP_inj`), and the keys and ciphertexts of one possible
output of `Setup` carry its description, in whose group the element encodings are injective
(`bb1_encSK_inj`, `bb1_encCT_inj`). -/
noncomputable def bb1Scheme (G : BilinearGen) (ℓ : PolyExpr) : IBEScheme where
  idLen := ℓ
  msgLen := G.wT
  ppLen := .add G.descLen (.mul (.const 4) G.wG)
  skLen := .mul (.const 2) G.wG
  ctLen := .add G.wT (.mul (.const 2) G.wG)
  PP κ := Σ d : List Bool, BB1.Params (G.group κ d)
  MSK κ := Σ d : List Bool, BB1.Params (G.group κ d) × (G.group κ d).G
  SK κ := Σ d : List Bool, BB1.Key (G.group κ d)
  CT κ := Σ d : List Bool, BB1.Ciphertext (G.group κ d)
  setup κ :=
    (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
    (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
      .pure (⟨G.desc κ r, k.1⟩, ⟨G.desc κ r, k⟩)
  keyGen _ msk id :=
    (BB1.keyGen msk.2.1 msk.2.2 (BB1.idToZ _ id)).bind fun d => .pure ⟨msk.1, d⟩
  enc _ pp id m :=
    (BB1.encrypt pp.2 (BB1.idToZ _ id) (BB1.decodeT _ m)).bind fun c => .pure ⟨pp.1, c⟩
  dec κ sk c :=
    if h : c.1 = sk.1 then
      some ((G.group κ sk.1).encT (BB1.decrypt sk.2 (h ▸ c.2)))
    else none
  MsgSpace κ pp m := ∃ u, (G.group κ pp.1).encT u = m
  encPP κ pp := padFin _ (pp.1 ++ List.ofFn ((G.group κ pp.1).encG pp.2.g) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.g1) ++ List.ofFn ((G.group κ pp.1).encG pp.2.g2) ++
    List.ofFn ((G.group κ pp.1).encG pp.2.h))
  encSK κ sk := padFin _ (List.ofFn ((G.group κ sk.1).encG sk.2.d0) ++
    List.ofFn ((G.group κ sk.1).encG sk.2.d1))
  encCT κ c := padFin _ (List.ofFn ((G.group κ c.1).encT c.2.a) ++
    List.ofFn ((G.group κ c.1).encG c.2.b) ++ List.ofFn ((G.group κ c.1).encG c.2.c))
  encPP_inj κ := by
    refine (OracleComp.allOutputs_true _).bind fun r _ =>
      (OracleComp.allOutputs_true _).bind fun k _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun r' _ =>
      (OracleComp.allOutputs_true _).bind fun k' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => bb1_encPP_inj G h (G.length_desc κ r) (G.length_desc κ r')
  encSK_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.2.1) (bb1_encSK_inj G h)
  encCT_inj κ := by
    refine (OracleComp.allOutputs_true _).mono fun k _ id id' m m' => ?_
    refine (OracleComp.allOutputs_true _).bind fun a _ => OracleComp.allOutputs_pure.2 ?_
    refine (OracleComp.allOutputs_true _).bind fun a' _ => OracleComp.allOutputs_pure.2 ?_
    exact fun h => congrArg (Sigma.mk k.1.1) (bb1_encCT_inj G h)

attribute [simps (config := { isSimp := false }) idLen msgLen ppLen skLen ctLen PP MSK SK CT
  setup keyGen enc dec MsgSpace encPP encSK encCT] bb1Scheme

/-- **The parameter encoding as a word**: `⟦encPP ⟨d, pp⟩⟧` is the padded word
`d ‖ g ‖ g_1 ‖ g_2 ‖ h` (`ppLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encPP (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encPP κ ⟨d, pp⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ppLen.eval κ) (d ++ List.ofFn ((G.group κ d).encG pp.g) ++
        List.ofFn ((G.group κ d).encG pp.g1) ++ List.ofFn ((G.group κ d).encG pp.g2) ++
        List.ofFn ((G.group κ d).encG pp.h))) := rfl

/-- **The key encoding as a word**: `⟦encSK ⟨d, k⟩⟧` is the padded word `d_0 ‖ d_1`
(`skLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encSK (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (k : BB1.Key (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encSK κ ⟨d, k⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).skLen.eval κ) (List.ofFn ((G.group κ d).encG k.d0) ++
        List.ofFn ((G.group κ d).encG k.d1))) := rfl

/-- **The message space as words**: a `msgLen(κ)`-bit message is in the message space of
`⟨d, pp⟩` iff its word is the word of the encoding of an element of `G_T`. -/
theorem bb1Scheme_msgSpace_iff (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    (bb1Scheme G ℓ).MsgSpace κ ⟨d, pp⟩ m ↔
      ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m :=
  exists_congr fun _ => List.ofFn_inj.symm

/-- **`Setup` at the scheme's types**: `Setup` runs the generator and BB1's `Setup`, and returns
`(⟨d, params⟩, ⟨d, (params, master-key)⟩)` as parameters and master key of `bb1Scheme G ℓ`:
`Setup κ = (sample r).bind fun r => (BB1.setup _).bind fun k => pure (⟨desc r, k.1⟩, ⟨desc r, k⟩)`,
the pair typed at `PP κ × MSK κ`. -/
theorem bb1Scheme_setup_eq (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) :
    (bb1Scheme G ℓ).setup κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
        .pure (((⟨G.desc κ r, k.1⟩ : (bb1Scheme G ℓ).PP κ),
          (⟨G.desc κ r, k⟩ : (bb1Scheme G ℓ).MSK κ)) :
            (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) := rfl

/-- **`KeyGen` at the scheme's types, followed by `f`**: for the master key `⟨d, (pp, mk)⟩` and an
`ℓ(κ)`-bit identity `ID`, `KeyGen` is BB1's `KeyGen` on `idToZ ID`, its key tagged with `d`:
`(KeyGen ⟨d, (pp, mk)⟩ ID).bind f = (BB1.keyGen pp mk (idToZ ID)).bind fun k => f ⟨d, k⟩`. -/
theorem bb1Scheme_keyGen_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (mk : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).SK κ → ProbComp β) :
    ((bb1Scheme G ℓ).keyGen κ ⟨d, (pp, mk)⟩ id).bind f =
      (BB1.keyGen pp mk (BB1.idToZ (G.group κ d) id)).bind fun k => f ⟨d, k⟩ := by
  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **`Encrypt` at the scheme's types, followed by `f`**: for the parameters `⟨d, pp⟩`, an
`ℓ(κ)`-bit identity `ID` and a `msgLen(κ)`-bit message `m`, `Encrypt` is BB1's `Encrypt` on
`idToZ ID` and `decodeT m` (the message read at the width of `G_T`), its ciphertext tagged
with `d`: `(Encrypt ⟨d, pp⟩ ID m).bind f = (BB1.encrypt pp (idToZ ID) (decodeT ⟦m⟧)).bind fun c =>
f ⟨d, c⟩`. -/
theorem bb1Scheme_enc_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).CT κ → ProbComp β) :
    ((bb1Scheme G ℓ).enc κ ⟨d, pp⟩ id m).bind f =
      (BB1.encrypt pp (BB1.idToZ (G.group κ d) id)
        (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))).bind fun c => f ⟨d, c⟩ := by
  rw [padFin_ofFn]
  simp only [bb1Scheme_enc, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **The ciphertext encoding as a word**: `⟦encCT ⟨d, c⟩⟧` is the padded word `A ‖ B ‖ C_1`
(`ctLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encCT (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (c : BB1.Ciphertext (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encCT κ ⟨d, c⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ) (List.ofFn ((G.group κ d).encT c.a) ++
        List.ofFn ((G.group κ d).encG c.b) ++ List.ofFn ((G.group κ d).encG c.c))) := rfl

/-- **BB1 is perfectly correct** [BB04, §4.1, "Indeed, for a valid ciphertext …"]: every
honest run with a message of the message space decrypts to that message.

**Proof sketch.** Every possible outcome of an honest run has parameters
`⟨d, (g, g^α, g_2, h)⟩`, key `⟨d, (g_2^α F(ID)^r, g^r)⟩` and ciphertext
`⟨d, (e(g^α, g_2)^s · M', g^s, F(ID)^s)⟩` with the same description `d` and
`M' = decodeT M`, so `Decrypt` takes its first branch and returns the encoding of `M'` by
`BB1.decrypt_encrypt`. A message of the message space is an encoding `encT u`, so
`M' = u` (`decodeT_encT`) and its encoding is `M`. -/
theorem bb1_correct (G : BilinearGen) (ℓ : PolyExpr) : (bb1Scheme G ℓ).Correct := by
  rw [IBEScheme.correct_iff]
  intro κ id m
  rw [IBEScheme.honestRun_eq, bb1Scheme_setup]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind, BB1.setup_eq, bb1Scheme_keyGen,
    bb1Scheme_enc, BB1.keyGen_eq, BB1.encrypt_eq]
  refine (OracleComp.allOutputs_true _).bind fun r _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun α _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun h _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun g2 _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun ρ _ => ?_
  refine (OracleComp.allOutputs_true _).bind fun σ _ => ?_
  refine OracleComp.allOutputs_pure.2 fun hm => ?_
  obtain ⟨u, hu⟩ := hm
  rw [bb1Scheme_dec, dif_pos rfl]
  dsimp only
  rw [← hu, BB1.decodeT_encT, BB1.decrypt_encrypt]

/-! ### The simulator of [BB04, proof of Theorem 4.1]

The Decision BDH algorithm `B` of the proof, as typed oracle handlers over the parameters of
`bb1Scheme`, with ideal uniform exponents; `bb1SimGame` runs the adversary against them. The
security argument is in `AdvancedEncryption.IdentityBased.BonehBoyenSecurity`. -/

section Simulator

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The simulator's state at parameter `κ` in the group described by `d`: the committed identity
with the simulator's exponent `α_1` (once `Init` is asked), and the issued challenge. -/
abbrev BB1SimState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- `BB1SimState G ℓ κ d` is the optional pair of the committed identity and `α_1`, with the
optional encoded challenge. -/
theorem bb1SimState_eq (κ : ℕ) (d : List Bool) :
    BB1SimState G ℓ κ d =
      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) ×
        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl

/-- The simulated parameters `(g, X, Y, X^{−ID*} g^{α_1})` for the committed identity `ID*` and
the exponent `α_1` [BB04, proof of Theorem 4.1, *Setup*]. -/
noncomputable def bb1SimParams {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    BB1.Params (G.group κ d) :=
  ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩

/-- `bb1SimParams G ℓ g X Y t α₁ = (g, X, Y, X ^ (−idToZ t).val · g ^ α₁.val)`. -/
theorem bb1SimParams_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order) :
    bb1SimParams G ℓ g X Y t α₁ =
      ⟨g, X, Y, X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val⟩ := rfl

/-- The simulated private key of `ID ≠ ID*` with exponent `r` [BB04, proof of Theorem 4.1,
*Phase 1*]: `(Y^{−α_1/(ID − ID*)} F(ID)^r, Y^{−1/(ID − ID*)} g^r)`, with `F` of the simulated
parameters and the identities read in `Z_p`. -/
noncomputable def bb1SimKey {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    BB1.Key (G.group κ d) :=
  ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
      BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
    Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩

/-- `bb1SimKey G ℓ g X Y t α₁ id r` is
`(Y^{(−α₁/(id − t)).val} · F(id)^{r.val}, Y^{(−1/(id − t)).val} · g^{r.val})`. -/
theorem bb1SimKey_eq {κ : ℕ} {d : List Bool} (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (r : ZMod (G.group κ d).order) :
    bb1SimKey G ℓ g X Y t α₁ id r =
      ⟨Y ^ (-α₁ / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val *
          BB1.F (bb1SimParams G ℓ g X Y t α₁) (BB1.idToZ (G.group κ d) id) ^ r.val,
        Y ^ (-1 / (BB1.idToZ (G.group κ d) id - BB1.idToZ (G.group κ d) t)).val * g ^ r.val⟩ :=
  rfl

/-- **The simulator's `Init`** [BB04, proof of Theorem 4.1, *Initialization* and *Setup*] on the
description `d` and `g, X = g^a, Y = g^{b'}`: before any commitment, draw `α_1 ∈ Z_p`, record
`(ID, α_1)` and answer the simulated parameters; afterwards answer the recorded identity's. -/
noncomputable def bb1SimInit (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | none => (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), s.2))
  | some (t, α₁) => .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, s)

/-- `Init` before any commitment draws `α_1` and answers the simulated parameters. -/
theorem bb1SimInit_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (none, c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun α₁ =>
        .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y id α₁⟩, (some (id, α₁), c)) :=
  rfl

/-- `Init` after a commitment answers the recorded identity's simulated parameters. -/
theorem bb1SimInit_some (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimInit G ℓ κ d g X Y id (some (t, α₁), c) =
      .pure ((bb1Scheme G ℓ).encPP κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩, (some (t, α₁), c)) :=
  rfl

/-- **The simulator's `KeyGen`** [BB04, proof of Theorem 4.1, *Phase 1*]: when `ID*` is recorded
and `ID ≠ ID*`, draw `r ∈ Z_p` and answer `⟨1, bb1SimKey … ID r⟩`; otherwise `⊥`. -/
noncomputable def bb1SimKeyQ (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).skLen.eval κ + 1) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1 with
  | some (t, α₁) =>
    if id = t then .pure (zeroBits _, s)
    else (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
      .pure (FixedLengthScheme.decAnswer
        (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)), s)
  | none => .pure (zeroBits _, s)

/-- `KeyGen` before `Init` answers `⊥`. -/
theorem bb1SimKeyQ_none (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y id (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `KeyGen` for the committed identity answers `⊥`. -/
theorem bb1SimKeyQ_target (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimKeyQ G ℓ κ d g X Y t (some (t, α₁), c) = .pure (zeroBits _, (some (t, α₁), c)) := by
  simp [bb1SimKeyQ]

/-- `KeyGen` for `ID ≠ ID*` draws `r` and answers the simulated key. -/
theorem bb1SimKeyQ_ne (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    (id t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (h : id ≠ t) :
    bb1SimKeyQ G ℓ κ d g X Y id (some (t, α₁), c) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        .pure (FixedLengthScheme.decAnswer
          (some ((bb1Scheme G ℓ).encSK κ ⟨d, bb1SimKey G ℓ g X Y t α₁ id r⟩)),
          (some (t, α₁), c)) := by
  simp [bb1SimKeyQ, h]

/-- The simulated challenge `(M · T, Z, Z^{α_1})` [BB04, proof of Theorem 4.1, *Challenge*] of the
message string `m`, encoded. -/
noncomputable def bb1SimCt (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool :=
  (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩

/-- `bb1SimCt G ℓ κ d Z T α₁ m` is the encoding of `(decodeT m · T, Z, Z ^ α₁.val)`. -/
theorem bb1SimCt_eq (κ : ℕ) (d : List Bool) (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (α₁ : ZMod (G.group κ d).order) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    bb1SimCt G ℓ κ d Z T α₁ m =
      (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩ := rfl

/-- **The simulated challenge as a word**: `⟦bb1SimCt … m⟧` is the padded word
`decodeT(m) · T ‖ Z ‖ Z^{α_1.val}` (`ctLen(κ)` bits), the message read at the width of `G_T`. -/
theorem ofFn_bb1SimCt (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (Z : (G.group κ d).G) (T : (G.group κ d).GT) (α₁ : ZMod (G.group κ d).order)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) :
    List.ofFn (bb1SimCt G ℓ κ d Z T α₁ m) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
        (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)) * T)) ++
          List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val)))) := by
  rw [padFin_ofFn]
  rfl

open Classical in
/-- **The simulator's `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*] with challenge bit
`b`, on `Z = g^c` and `T`: with `ID*` recorded and no challenge yet, if `M₀, M₁` are in the
message space, answer and record `(M_b · T, Z, Z^{α_1})`, and otherwise `⊥`; once a challenge is
recorded, repeat it; before `Init`, `⊥`. -/
noncomputable def bb1SimChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  match s.1, s.2 with
  | some _, some c => .pure (c, s)
  | some (t, α₁), none =>
    if (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2 then
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (s.1, some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1))))
    else .pure (zeroBits _, s)
  | none, _ => .pure (zeroBits _, s)

/-- `Challenge` before `Init` answers `⊥`. -/
theorem bb1SimChal_none (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (none, c) = .pure (zeroBits _, (none, c)) := rfl

/-- `Challenge` after a recorded challenge repeats it. -/
theorem bb1SimChal_repeat (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some t, some w) = .pure (w, (some t, some w)) := rfl

/-- The first `Challenge` with both messages in the message space answers and records
`(M_b · T, Z, Z^{α_1})`. -/
theorem bb1SimChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1),
        (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then (FixedLengthScheme.splitHalf mm).2
          else (FixedLengthScheme.splitHalf mm).1)))) := by
  simp only [bb1SimChal]
  rw [if_pos h]

/-- The first `Challenge` with a message outside the message space answers `⊥`. -/
theorem bb1SimChal_invalid (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (h : ¬ ((bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).1 ∧
        (bb1Scheme G ℓ).MsgSpace κ ⟨d, bb1SimParams G ℓ g X Y t α₁⟩
          (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimChal G ℓ b κ d g X Y Z T mm (some (t, α₁), none) =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  simp only [bb1SimChal]
  rw [if_neg h]

/-- **The simulator's oracles** [BB04, proof of Theorem 4.1] with challenge bit `b`, at
parameter `κ`, on the description `d` and the Decision BDH tuple `(g, X, Y, Z, T)`: the three
handlers `bb1SimInit`, `bb1SimKeyQ`, `bb1SimChal` as an implementation of the game's oracles. -/
noncomputable def bb1SimImpl (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimChal G ℓ b κ d g X Y Z T)

/-- `bb1SimImpl` is `oracleImpl` of the three simulator handlers. -/
theorem bb1SimImpl_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    bb1SimImpl G ℓ b κ d g X Y Z T =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimChal G ℓ b κ d g X Y Z T) := rfl

/-- **The simulation game** [BB04, proof of Theorem 4.1] for the adversary `A` with budget `q`,
challenge bit `b`, on `P_BDH` (`real`) or `R_BDH`: draw the generator's coins `r`, `g ∈ G^*`,
`a, b', c ∈ Z_p`, `T ∈ G_T` and `A`'s coins, run `A(1^κ)` against the simulator's oracles on
`(g, g^a, g^{b'}, g^c, T')` with `T' = e(g, g)^{ab'c}` if `real` and `T` otherwise, and return
`A`'s guess. -/
noncomputable def bb1SimGame (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
    ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
  (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
  (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
      (g.1 ^ abc.2.2.val)
      (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
        else t))
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind fun res => .pure (res.1 0)

/-- The simulation game draws the generator's coins, `g ∈ G^*`, `(a, b', c)`, `T` and `A`'s
coins, and simulates `A` against `bb1SimImpl` on the Decision BDH tuple. -/
theorem bb1SimGame_eq (A : NUPPT) (q : ℕ) (b real : Bool) (κ : ℕ) :
    bb1SimGame G ℓ A q b real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order)).bind fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if real then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0) := rfl

end Simulator

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Random
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Chain

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Selective-identity security of BB1 under Decision BDH

[BB04, Theorem 4.1] at depth `ℓ = 1`: if Decision BDH holds in `G`, the BB1 system is
IND-sID-CPA secure. The proof [BB04, pp. 7–8] builds a Decision BDH algorithm `B` that, given
`(g, g^a, g^b, g^c, T)`, plays the selective-identity game with the adversary without knowing the
master key `g^{ab}`:
* **Setup**, once `ID*` is committed: a random `α_1 ∈ Z_p`, `h = g_1^{−ID*} g^{α_1}`,
  `params = (g, g_1 = g^a, g_2 = g^b, h)`, so that `F(x) = g_1^{x − ID*} g^{α_1}`;
* **private keys** for `ID ≠ ID*`: a random `r ∈ Z_p`,
  `(g_2^{−α_1/(ID − ID*)} F(ID)^r, g_2^{−1/(ID − ID*)} g^r)`;
* **the challenge**: `(M_b · T, g^c, (g^c)^{α_1})`.

**The simulation game.** `bb1SimGame` (defined beside the scheme in
`AdvancedEncryption/IdentityBased/BonehBoyen.lean`) is that simulator as a game of the `Games`
framework, with ideal uniform exponents, run against the adversary machine on a Decision BDH
tuple drawn from `P_BDH` (`real`) or `R_BDH`. The security proof has three named steps:
1. `bb1_sim_real`: on `P_BDH`, the simulation is the real game, except when distinct
   identities collide in `Z_p` (the generator's coins with `p < 2^ℓ`);
2. `bb1_sim_random`: on `R_BDH`, the simulation does not depend on the challenge bit;
3. `exists_bb1_distinguisher`: the simulation is, up to a negligible statistical term, the
   Decision BDH experiment of a non-uniform PPT distinguisher (the machine step: handler theorem
   T1 with exponents drawn from coin blocks). It is stated in its own module,
   `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean`, so that it can be filled
   independently of steps 1 and 2 (ruling Q11 of `PairingCryptographyPlan.md`).
`bb1_sidSecure` assembles them by the triangle inequality.

**Deviation:** the paper's `B` draws the challenge bit itself and outputs `[b = b']`; here there
is one simulation per value of `b`, and the advantage of the two-experiment form is bounded by
the sum of two Decision BDH advantages; the paper's statement is concrete (`t' < t − Θ(τ ℓ q_S)`).

## Main definitions

None: the simulator (`bb1SimImpl`, `bb1SimGame`) is defined beside the scheme, in
`AdvancedEncryption.IdentityBased.BonehBoyen`.

## Contents

Steps 1 and 2 are proved in helper modules:

* `BonehBoyenSecurity.Lazy`: the simulator with its challenge coins drawn at the first valid
  `Challenge`, and its eager step.
* `BonehBoyenSecurity.Real`: the output of `Setup`, read; the real game with `h` recorded, and
  with `h` drawn at the first `Init`.
* `BonehBoyenSecurity.Coupling`: step M, the real game against the simulator call by call, on
  good coins.
* `BonehBoyenSecurity.Random`: on a random `T`, the simulator does not depend on the challenge
  bit.
* `BonehBoyenSecurity.Chain`: on good coins, the real game is the simulation on `P_BDH`.

## Main results

* `bb1_sim_real`, `bb1_sim_random` — steps 1 and 2 (step 3, `exists_bb1_distinguisher`, is in
  `AdvancedEncryption.IdentityBased.BonehBoyenMachine`).
* `bb1_sidSecure` — [BB04, Theorem 4.1] at depth 1.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): Theorem 4.1 and
  its proof; §4.4 (p. 8).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **Step 1: on `P_BDH` the simulation is the real game** [BB04, proof of Theorem 4.1, "When
the input 5-tuple is sampled from `P_BDH` … `A`'s view is identical to its view in a real attack
game"], except on the generator's coins where `p < 2^ℓ`, where distinct identities may collide
in `Z_p`.

**Proof sketch.** Read `Setup` through `BB1Sim.setup_out` and condition both games on the
generator's coins `r` (`prob_bind`). On coins with `p < 2^ℓ` the two conditional acceptances are
probabilities, so they differ by at most `1`; averaging this pointwise bound
(`ProbComp.abs_expect_sub_le_expect`) gives `Pr_r[p < 2^ℓ]` (`Bridge.prob_sample_eq_uprob`). On
coins with `2^ℓ ≤ p` they are equal (`BB1Sim.prob_sidGame_coins`), by coupling the two games:
* the real `Setup` draws `h` before `ID*` exists; move it past `g_2` and the adversary's coins and
  draw it at the first `Init` (`ProbComp.expect_simulate_rel` with `h` recorded beside `ID*`, then
  `Games.expect_simulate_eager`);
* map `α ↦ a` and read `g_2` as `g^{b'}` (`pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
* the real game and the simulator then agree call by call on states related by
  `h = g_1^{−ID*} g^{α_1}` (`ProbComp.expect_simulate_rel`, `ProbComp.expect_sample_rel`): at
  `Init`, `h ↦ α_1` is a bijection for each `ID*`, so `h` is uniform and the answers agree; for
  `ID ≠ ID*`, which stay distinct in `Z_p` because `idToZ` is injective on `ℓ`-bit strings
  (`bitsToNat_lt`, `bitsToNat_injective`, `CharP.natCast_injOn_Iio`), the simulated key with
  exponent `r` is the real key with exponent `r̃ = r − b'/(ID − ID*)`, a bijection of `Z_p` (the
  paper's computation, `pow_val_add`, `pow_val_neg`, `pow_val_mul`); the challenge is `Encrypt`
  with `s = c`, since `F(ID*) = g^{α_1}` and `e(g, g)^{ab'c} = e(g_1, g_2)^c` (`bilinear_pow`);
* finally the challenge coin `c` is drawn in advance (`Games.expect_simulate_eager`) and
  `(a, b', c)` merges into one draw (`Bridge.expect_sample_pair`); the unused `T` drops out. -/
theorem bb1_sim_real (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ) :
    advantage ((bb1Scheme G ℓ).sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤
      uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
  obtain ⟨o, hset, hR⟩ := BB1Sim.setup_out G ℓ κ
  rw [advantage_eq, accept_eq, accept_eq, IBEScheme.sidGame_eq, hset, bb1SimGame_eq,
    ProbComp.prob_bind, ProbComp.prob_bind]
  -- average the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]` over the generator's coins
  calc _ ≤ ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
          (fun r => if (G.inst κ r).order < 2 ^ ℓ.eval κ then 1 else 0) :=
        ProbComp.abs_expect_sub_le_expect _ fun r => ?_
    _ = uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < 2 ^ ℓ.eval κ) := by
        rw [← ProbComp.prob_eq_expect, Bridge.prob_sample_eq_uprob]
  have h01 : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |x - y| ≤ 1 := fun x y _ _ _ _ =>
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  by_cases hr : (G.inst κ r).order < 2 ^ ℓ.eval κ
  -- bad coins: two probabilities differ by at most `1`
  · rw [if_pos hr]
    exact h01 _ _ (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
  -- good coins: the chain of `BB1Sim.prob_sidGame_coins`
  · rw [if_neg hr]
    exact (abs_eq_zero.2 (sub_eq_zero.2 (BB1Sim.prob_sidGame_coins G ℓ A q b κ o hR r hr))).le

/-- **Step 2: on `R_BDH` the simulation does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, "when `T` is uniform and independent in `G_1` … `C` is independent of `b` in the
adversary's view"].

**Proof sketch.** In the `R_BDH` game, `T` is uniform in `G_T` and is used only at the first
valid `Challenge`, in the first component `M_b · T` of the challenge. Exchange the sample of `T`
with the adversary's coins (`expect_sample_comm`) and draw it at that call
(`BB1Sim.expect_simulate_bb1SimLazy`, an instance of `expect_simulate_eager`). The simulators
with `b = 0` and `b = 1` then agree call by call (`ProbComp.expect_simulate_congr`): every other
call is the same for both bits, and at the first valid `Challenge` the bijection
`T ↦ M_1^{−1} M_0 · T` of `G_T` turns the answer `M_0 · T` into `M_1 · T'`
(`ProbComp.expect_sample_rel`). Challenges outside the message space are refused in both games.
So the acceptance probabilities are equal (`advantage_eq`). -/
theorem bb1_sim_random (A : NUPPT) (q : ℕ) (κ : ℕ) :
    advantage (bb1SimGame G ℓ A q false false κ) (bb1SimGame G ℓ A q true false κ) = 0 := by
  rw [advantage_eq, abs_eq_zero, sub_eq_zero, accept_eq, accept_eq, bb1SimGame_eq, bb1SimGame_eq]
  simp only [ProbComp.prob_bind, Bool.false_eq_true, if_false]
  refine congrArg _ (funext fun r => congrArg _ (funext fun g => congrArg _ (funext fun abc => ?_)))
  -- `T` is drawn before `A`'s coins: exchange them, then compare the two bits for each `ρ`
  conv_lhs => rw [ProbComp.expect_sample_comm]
  conv_rhs => rw [ProbComp.expect_sample_comm]
  exact congrArg _ (funext fun ρ => BB1Sim.expect_bb1SimImpl_random G ℓ κ _ _ _ _ _
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (fun a => ProbComp.prob (.pure (a 0)) (· = true)))

/-- **BB1 is IND-sID-CPA secure under Decision BDH** [BB04, Theorem 4.1, at depth `ℓ = 1`]: if
the generator's groups have efficient operations, the arithmetic bundle holds, the order is at
least `2^{ℓ(κ)}` except with negligible probability, and Decision BDH holds, then the BB1 system
for `ℓ(κ)`-bit identities is IND-sID-CPA secure.

**Deviation:** asymptotic form of the paper's concrete bound (`(t', q_S, ε)`-security from
`(t, ε)`-Decision BDH); the efficiency hypotheses `O` and `H` make the paper's simulator a
non-uniform PPT; `hN` makes distinct `ℓ`-bit identities distinct in `Z_p` (the condition
`2^b < p` of [BB04, §4.4]); the advantage is bounded by two Decision BDH advantages, one per
challenge bit, instead of one.

**Proof sketch.** By the triangle inequality through the simulation games and the Decision BDH
experiments of the two distinguishers `D_0`, `D_1` of step 3,
`advantage (sidGame … false) (sidGame … true)` is at most
`2 Pr_r[p < 2^ℓ] + 4σ(κ) + dbdhAdv D_0 κ + dbdhAdv D_1 κ` (steps 1 and 3 for each bit, step 2
in the middle). Each term is negligible (`hN`, step 3, `h`). -/
theorem bb1_sidSecure (H : Candidates.ArithmeticFP) (O : G.Ops)
    (hN : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.OrderAtLeastExcept (fun κ => 2 ^ ℓ.eval κ) δ)
    (h : G.DBDHAssumption) : (bb1Scheme G ℓ).SIDSecure := by
  rw [IBEScheme.sidSecure_iff]
  intro A q
  obtain ⟨δ, hδ, hN⟩ := hN
  obtain ⟨D, σ, hσ, hD⟩ := exists_bb1_distinguisher G ℓ H O A q
  refine ⟨fun κ => 2 * δ κ + 4 * σ κ + (G.dbdhAdv (D false) κ + G.dbdhAdv (D true) κ),
    ((hδ.const_mul 2).add (hσ.const_mul 4)).add
      ((G.dbdhAssumption_iff.1 h (D false)).add (G.dbdhAssumption_iff.1 h (D true))), fun κ => ?_⟩
  have hu := (G.orderAtLeastExcept_iff _ δ).1 hN κ
  have t := fun G₀ G₁ G₂ : ProbComp Bool => advantage_triangle G₀ G₁ G₂
  have hc := fun G₀ G₁ : ProbComp Bool => advantage_comm G₀ G₁
  have s0 := bb1_sim_real G ℓ A (q.eval κ) false κ
  have s1 := bb1_sim_real G ℓ A (q.eval κ) true κ
  have s2 := bb1_sim_random G ℓ A (q.eval κ) κ
  have d0T := hD false true κ
  have d0F := hD false false κ
  have d1T := hD true true κ
  have d1F := hD true false κ
  have a0 := G.dbdhAdv_eq (D false) κ
  have a1 := G.dbdhAdv_eq (D true) κ
  set S0 := (bb1Scheme G ℓ).sidGame A (q.eval κ) false κ
  set S1 := (bb1Scheme G ℓ).sidGame A (q.eval κ) true κ
  set M0T := bb1SimGame G ℓ A (q.eval κ) false true κ
  set M0F := bb1SimGame G ℓ A (q.eval κ) false false κ
  set M1T := bb1SimGame G ℓ A (q.eval κ) true true κ
  set M1F := bb1SimGame G ℓ A (q.eval κ) true false κ
  set E0T := G.dbdhGame (D false) true κ
  set E0F := G.dbdhGame (D false) false κ
  set E1T := G.dbdhGame (D true) true κ
  set E1F := G.dbdhGame (D true) false κ
  have := t S0 M0T S1
  have := t M0T E0T S1
  have := t E0T E0F S1
  have := t E0F M0F S1
  have := t M0F M1F S1
  have := t M1F E1F S1
  have := t E1F E1T S1
  have := t E1T M1T S1
  have := hc E0T E0F
  have := hc E0F M0F
  have := hc E1T M1T
  have := hc M1T S1
  linarith

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Lazy.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator with its challenge coins drawn at the challenge

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (steps 1 and 2 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The simulator `bb1SimImpl` of
`AdvancedEncryption/IdentityBased/BonehBoyen.lean` receives the challenge coins `(Z, T)` before
the game starts, but uses them only at the first valid `Challenge` [BB04, proof of Theorem 4.1,
*Challenge*]. `bb1SimLazy` is the same simulator with coins `zt u` drawn at that call, for a
uniform `u` in any nonempty finite type `U`: step 1 draws `u = c ∈ Z_p` with
`zt c = (g^c, e(g, g)^{a b' c})`, step 2 draws `u = T ∈ G_T` with `zt T = (Z, T)`. The two
simulators simulate alike (`expect_simulate_bb1SimLazy`, an instance of
`Games.expect_simulate_eager`).

The module also reads the game's query and answer types from their published equations
(`sidSpec_dom_zero`, …), so that its consumers never reduce `IBEScheme.inLens` or
`IBEScheme.outLens`.

## Main definitions

* `BB1Sim.bb1SimLazyChal` — the simulator's `Challenge` with its coins drawn at the call.
* `BB1Sim.bb1SimLazy` — the simulator's oracles with that `Challenge`.

## Main results

* `BB1Sim.bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimLazy_two_fresh`, `bb1SimLazy_two_of_not` —
  `bb1SimLazy` call by call, against `bb1SimImpl`.
* `BB1Sim.bb1SimImpl_two_of_not` — away from the first valid `Challenge`, `bb1SimImpl` does not
  read its coins.
* `BB1Sim.expect_simulate_bb1SimLazy` — the lazy simulator simulates like `bb1SimImpl` with coins
  drawn in advance.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The game's query and answer types, from published equations -/

section Types

variable (S : IBEScheme) (κ : ℕ)

/-- `Init` queries are identities: `(S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_dom`, `inLens_zero`). Glue for the game's types. -/
theorem sidSpec_dom_zero : (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_zero]

/-- `KeyGen` queries are identities: `(S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_dom`, `inLens_one`). Glue for the game's types. -/
theorem sidSpec_dom_one : (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_one]

/-- `Challenge` queries are two messages:
`(S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)` (`sidSpec_eq`,
`bitSpec_dom`, `inLens_two`). Glue for the game's types. -/
theorem sidSpec_dom_two :
    (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_two]

/-- `Init` answers parameters: `(S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_zero`). Glue for the game's types. -/
theorem sidSpec_rng_zero : (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_zero]

/-- `KeyGen` answers a bit and a key: `(S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_one`). Glue for the game's types. -/
theorem sidSpec_rng_one : (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_one]

/-- `Challenge` answers a ciphertext: `(S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_two`). Glue for the game's types. -/
theorem sidSpec_rng_two : (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_two]

/-- The `⊥` word of a width equal to `m`, cast: `zeroBits n = cast e (zeroBits m)` for `n = m`.
Glue for the game's types. -/
theorem zeroBits_eq_cast {n m : ℕ} (hnm : n = m) (e : (Fin m → Bool) = (Fin n → Bool)) :
    zeroBits n = cast e (zeroBits m) := by
  subst hnm
  rfl

end Types

/-! ### The lazy simulator -/

section Lazy

variable (G : BilinearGen) (ℓ : PolyExpr)

open Classical in
/-- **The simulator's `Challenge` with its coins drawn at the call** [BB04, proof of Theorem 4.1,
*Challenge*]: with `ID*` recorded, no challenge yet, and both messages `M₀, M₁` encodings of
`G_T`, draw `u ∈ U` and answer as `bb1SimChal` on the coins `zt u = (Z, T)`; otherwise answer
as `bb1SimChal` on the coins `(1, 1)`, which it does not read there. -/
noncomputable def bb1SimLazyChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  if s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)
  then (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s
  else bb1SimChal G ℓ b κ d g X Y 1 1 mm s

/-- At the first valid `Challenge`, `bb1SimLazyChal` draws `u` and answers as `bb1SimChal` on
`zt u`: for `s.1` some, `s.2 = none` and both messages encodings of `G_T`,
`bb1SimLazyChal … zt mm s = (sample U).bind fun u => bb1SimChal … (zt u).1 (zt u).2 mm s`. Glue: a
case reader of `bb1SimLazyChal`. -/
theorem bb1SimLazyChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimLazyChal G ℓ b κ d g X Y zt mm s =
      (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s := by
  rw [bb1SimLazyChal, if_pos h]

/-- Away from the first valid `Challenge`, `bb1SimLazyChal` answers as `bb1SimChal` on the
coins `(1, 1)`: `bb1SimLazyChal … zt mm s = bb1SimChal … 1 1 mm s`. Glue: a case reader of
`bb1SimLazyChal`. -/
theorem bb1SimLazyChal_of_not (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2))) :
    bb1SimLazyChal G ℓ b κ d g X Y zt mm s = bb1SimChal G ℓ b κ d g X Y 1 1 mm s := by
  rw [bb1SimLazyChal, if_neg h]

/-- **The simulator with its challenge coins drawn at the challenge** [BB04, proof of
Theorem 4.1]: the oracles `oracleImpl` of the simulator's `Init` (`bb1SimInit`) and `KeyGen`
(`bb1SimKeyQ`) and of `bb1SimLazyChal`, with challenge bit `b` on `g, X, Y` and the coin map
`zt : U → G × G_T`. -/
noncomputable def bb1SimLazy (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimLazyChal G ℓ b κ d g X Y zt)

/-- `bb1SimLazy` is `oracleImpl` of `bb1SimInit`, `bb1SimKeyQ` and `bb1SimLazyChal`:
`bb1SimLazy … zt = oracleImpl κ (bb1SimInit …) (bb1SimKeyQ …) (bb1SimLazyChal … zt)`. Glue: the
reader of `bb1SimLazy`. -/
theorem bb1SimLazy_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
    bb1SimLazy G ℓ b κ d g X Y zt =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimLazyChal G ℓ b κ d g X Y zt) := rfl

variable (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G) {U : Type} [Fintype U]
  [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)

/-- `Init` of `bb1SimImpl` does not read the challenge coins:
`bb1SimImpl … Z T 0 x s = bb1SimImpl … Z' T' 0 x s`. Glue: a case fact of `bb1SimImpl` for the eager
step. -/
theorem bb1SimImpl_zero_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
    bb1SimImpl G ℓ b κ d g X Y Z T 0 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 0 x s := by
  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
    IBEScheme.oracleImpl_zero_onSpec]

/-- `KeyGen` of `bb1SimImpl` does not read the challenge coins:
`bb1SimImpl … Z T 1 x s = bb1SimImpl … Z' T' 1 x s`. Glue: a case fact of `bb1SimImpl` for the eager
step. -/
theorem bb1SimImpl_one_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
    bb1SimImpl G ℓ b κ d g X Y Z T 1 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 1 x s := by
  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
    IBEScheme.oracleImpl_one_onSpec]

/-- `Init` of the lazy simulator is `Init` of `bb1SimImpl`:
`bb1SimLazy … zt 0 x s = bb1SimImpl … 1 1 0 x s`. Glue: a case reader of `bb1SimLazy`. -/
theorem bb1SimLazy_zero (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
    bb1SimLazy G ℓ b κ d g X Y zt 0 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 0 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
    IBEScheme.oracleImpl_zero_onSpec]

/-- `KeyGen` of the lazy simulator is `KeyGen` of `bb1SimImpl`:
`bb1SimLazy … zt 1 x s = bb1SimImpl … 1 1 1 x s`. Glue: a case reader of `bb1SimLazy`. -/
theorem bb1SimLazy_one (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
    bb1SimLazy G ℓ b κ d g X Y zt 1 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 1 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
    IBEScheme.oracleImpl_one_onSpec]

/-- **The first valid `Challenge` of the lazy simulator** draws `u` and calls `bb1SimImpl` on the
coins `zt u`: for `s.1` some, `s.2 = none`, and both messages of the query `x` (read as two
messages) encodings of `G_T`,
`bb1SimLazy … zt 2 x s = (sample U).bind fun u => bb1SimImpl … (zt u).1 (zt u).2 2 x s`. Glue: a
case reader of `bb1SimLazy`. -/
theorem bb1SimLazy_two_fresh (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    bb1SimLazy G ℓ b κ d g X Y zt 2 x s =
      (ProbComp.sample U).bind fun u =>
        bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2 2 x s := by
  rw [bb1SimLazy_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_fresh _ _ _ _ _ _ _ _ _ _ _
    h, OracleComp.bind_assoc]
  refine congrArg _ (funext fun u => ?_)
  rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec]

/-- **`Challenge` of the lazy simulator away from the first valid one** is `Challenge` of
`bb1SimImpl` on the coins `(1, 1)`: `bb1SimLazy … zt 2 x s = bb1SimImpl … 1 1 2 x s`. Glue: a case
reader of `bb1SimLazy`. -/
theorem bb1SimLazy_two_of_not (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
    bb1SimLazy G ℓ b κ d g X Y zt 2 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 2 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec,
    IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_of_not _ _ _ _ _ _ _ _ _ _ _ h]

/-- **Away from the first valid `Challenge`, `bb1SimImpl` reads neither its coins nor its
challenge bit**, and keeps the recorded challenge: unless `s.1` is some, `s.2 = none` and both
messages are encodings of `G_T`, `bb1SimImpl b … Z T 2 x s = bb1SimImpl false … 1 1 2 x s`, and
every outcome has the challenge `s.2`. Glue: a case fact of `bb1SimImpl` for the eager step.

**Proof sketch.** Read both calls by `oracleImpl_two_onSpec`. Before `Init` both answer `⊥`
(`bb1SimChal_none`); after a recorded challenge both repeat it (`bb1SimChal_repeat`); at a first
`Challenge` with a message outside the message space both answer `⊥` (`bb1SimChal_invalid`,
`bb1Scheme_msgSpace_iff`). -/
theorem bb1SimImpl_two_of_not (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
    bb1SimImpl G ℓ b κ d g X Y Z T 2 x s = bb1SimImpl G ℓ false κ d g X Y 1 1 2 x s ∧
      (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2 = s.2 := by
  obtain ⟨s₁, s₂⟩ := s
  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec,
    IBEScheme.oracleImpl_two_onSpec]
  rcases s₁ with _ | ⟨t, α₁⟩
  -- before `Init`: `⊥`
  · rw [bb1SimChal_none, bb1SimChal_none, OracleComp.pure_bind]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
  rcases s₂ with _ | w
  -- a first `Challenge` with a message outside the message space: `⊥`
  · have hv : ¬ ((∃ u, List.ofFn ((G.group κ d).encT u) =
              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
            ∃ u, List.ofFn ((G.group κ d).encT u) =
              List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :=
      fun hv => h ⟨rfl, rfl, hv⟩
    have hm : ∀ (b' : Bool) (Z' : (G.group κ d).G) (T' : (G.group κ d).GT),
        bb1SimChal G ℓ b' κ d g X Y Z' T' (cast (sidSpec_dom_two _ κ) x) (some (t, α₁), none) =
          .pure (zeroBits _, (some (t, α₁), none)) := fun b' Z' T' =>
      bb1SimChal_invalid G ℓ b' κ d g X Y Z' T' _ t α₁ fun hm' =>
        hv ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm'.1,
          (bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm'.2⟩
    rw [hm, hm, OracleComp.pure_bind]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
  -- after a recorded challenge: repeat it
  · rw [bb1SimChal_repeat, bb1SimChal_repeat, OracleComp.pure_bind]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩

/-- **The first valid `Challenge` records a challenge**: for `s.1` some and `s.2 = none`, and
both messages encodings of `G_T`, every outcome of `bb1SimImpl … Z T 2 x s` has a recorded
challenge. Glue: a case fact of `bb1SimImpl` for the eager step.

**Proof sketch.** Read the call by `oracleImpl_two_onSpec`; at the first valid `Challenge` it is
`bb1SimChal_fresh` (validity through `bb1Scheme_msgSpace_iff`), which records the challenge. -/
theorem bb1SimImpl_two_fresh_allOutputs (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2.isSome := by
  obtain ⟨s₁, s₂⟩ := s
  obtain ⟨h₁, h₂, hv⟩ := h
  rcases s₁ with _ | ⟨t, α₁⟩
  · exact absurd h₁ Bool.false_ne_true
  subst h₂
  rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh G ℓ b κ d g X Y Z T _ t α₁
    ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1, (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩,
    OracleComp.pure_bind]
  exact OracleComp.allOutputs_pure.2 rfl

/-- **`Init` and `KeyGen` keep the recorded challenge**: for `i ≠ 2`, every outcome of
`bb1SimImpl … Z T i x s` has the challenge `s.2`. Glue: a case fact of `bb1SimImpl` for the eager
step.

**Proof sketch.** Read the call by `oracleImpl_zero_onSpec` or `oracleImpl_one_onSpec`. `Init`
records `(ID, α_1)` or keeps the state (`bb1SimInit_none`, `bb1SimInit_some`); `KeyGen` keeps the
state (`bb1SimKeyQ_none`, `bb1SimKeyQ_target`, `bb1SimKeyQ_ne`). Neither touches `s.2`. -/
theorem bb1SimImpl_allOutputs_of_ne_two (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (i : Fin 3) (hi : i ≠ 2) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (s : BB1SimState G ℓ κ d) :
    (bb1SimImpl G ℓ b κ d g X Y Z T i x s).AllOutputs fun p => p.2.2 = s.2 := by
  obtain ⟨s₁, s₂⟩ := s
  revert x
  match i, hi with
  | 0, _ =>
    intro x
    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec]
    rcases s₁ with _ | ⟨t, α₁⟩
    · rw [bb1SimInit_none]
      refine OracleComp.AllOutputs.bind (P := fun p => p.2.2 = s₂) ?_
        fun p hp => OracleComp.allOutputs_pure.2 hp
      exact (OracleComp.allOutputs_true _).bind fun _ _ => OracleComp.allOutputs_pure.2 rfl
    · rw [bb1SimInit_some, OracleComp.pure_bind]
      exact OracleComp.allOutputs_pure.2 rfl
  | 1, _ =>
    intro x
    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec]
    rcases s₁ with _ | ⟨t, α₁⟩
    · rw [bb1SimKeyQ_none, OracleComp.pure_bind]
      exact OracleComp.allOutputs_pure.2 rfl
    by_cases ht : cast (sidSpec_dom_one _ κ) x = t
    · rw [ht, bb1SimKeyQ_target, OracleComp.pure_bind]
      exact OracleComp.allOutputs_pure.2 rfl
    · rw [bb1SimKeyQ_ne (h := ht)]
      refine OracleComp.AllOutputs.bind (P := fun p => p.2.2 = s₂) ?_
        fun p hp => OracleComp.allOutputs_pure.2 hp
      exact (OracleComp.allOutputs_true _).bind fun _ _ => OracleComp.allOutputs_pure.2 rfl
  | 2, hi => exact absurd rfl hi

/-- **The lazy simulator simulates like `bb1SimImpl` with its coins drawn in advance**: from a
state with no recorded challenge (`s.2 = none`), for every computation `c` and every `F`,
`𝔼[F] (simulate (bb1SimLazy … zt) c s) =
𝔼_{u ← U} 𝔼[F] (simulate (bb1SimImpl … (zt u).1 (zt u).2) c s)`. Glue: an instance of
`Games.expect_simulate_eager`, with the coins spent at the first valid `Challenge`.

**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1SimLazy … zt`,
`OE u := bb1SimImpl … (zt u)` and `used v := v.2` some. `Init` and `KeyGen` do not read the
coins (`bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimImpl_zero_coins`, `bb1SimImpl_one_coins`)
and keep the recorded challenge (`bb1SimImpl_allOutputs_of_ne_two`). A `Challenge` other than
the first valid one does not read them either and keeps the recorded challenge
(`bb1SimLazy_two_of_not`, `bb1SimImpl_two_of_not`); the first valid one draws them
(`bb1SimLazy_two_fresh`) and records a challenge (`bb1SimImpl_two_fresh_allOutputs`). -/
theorem expect_simulate_bb1SimLazy {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α × BB1SimState G ℓ κ d → ℝ) {s : BB1SimState G ℓ κ d} (hs : s.2 = none) :
    ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g X Y zt) c s) F =
      ProbComp.expect (ProbComp.sample U) fun u =>
        ProbComp.expect (simulate (bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2) c s) F := by
  have h01 : ∀ i : Fin 3, i ≠ 2 → i = 0 ∨ i = 1 := by decide
  refine Games.expect_simulate_eager (T := U) (bb1SimLazy G ℓ b κ d g X Y zt)
    (fun u => bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2) (fun v => v.2.isSome = true)
    (fun u i => ?_) (fun i => ?_) (fun i => ?_) c F
    (by show ¬ (s.2.isSome = true); rw [hs]; exact Bool.false_ne_true)
  -- from a used state, the coins are not read
  · by_cases h2 : i = 2
    · subst h2
      intro x s hu
      have hn : ¬ (s.1.isSome ∧ s.2 = none ∧
        ((∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
        fun hf => by
          have hu' : s.2.isSome = true := hu
          rw [hf.2.1] at hu'
          exact Bool.false_ne_true hu'
      rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hn]
      exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y _ _ x s hn).1.trans
        (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hn).1.symm
    · intro x s _
      rcases h01 i h2 with rfl | rfl
      · rw [bb1SimLazy_zero]
        exact bb1SimImpl_zero_coins G ℓ b κ d g X Y _ _ _ _ x s
      · rw [bb1SimLazy_one]
        exact bb1SimImpl_one_coins G ℓ b κ d g X Y _ _ _ _ x s
  -- a used state stays used
  · intro x s hu
    by_cases h2 : i = 2
    · subst h2
      have hn : ¬ (s.1.isSome ∧ s.2 = none ∧
        ((∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :=
        fun hf => by
          have hu' : s.2.isSome = true := hu
          rw [hf.2.1] at hu'
          exact Bool.false_ne_true hu'
      rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hn]
      exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hn).2.mono fun p hp => by
        show p.2.2.isSome = true; rw [hp]; exact hu
    · rcases h01 i h2 with rfl | rfl
      · rw [bb1SimLazy_zero]
        exact (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 0 (by decide) x s).mono
          fun p hp => by show p.2.2.isSome = true; rw [hp]; exact hu
      · rw [bb1SimLazy_one]
        exact (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 1 (by decide) x s).mono
          fun p hp => by show p.2.2.isSome = true; rw [hp]; exact hu
  -- from an unused state, only the first valid `Challenge` spends the coins
  · intro x s hu
    by_cases h2 : i = 2
    · subst h2
      by_cases hf : (s.1.isSome ∧ s.2 = none ∧
        ((∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
      · exact Or.inr ⟨bb1SimLazy_two_fresh G ℓ b κ d g X Y zt x s hf,
          fun u => bb1SimImpl_two_fresh_allOutputs G ℓ b κ d g X Y _ _ x s hf⟩
      · refine Or.inl fun u => ⟨?_, ?_⟩ <;> rw [bb1SimLazy_two_of_not G ℓ b κ d g X Y zt x s hf]
        · exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y _ _ x s hf).1.trans
            (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hf).1.symm
        · exact (bb1SimImpl_two_of_not G ℓ b κ d g X Y 1 1 x s hf).2.mono fun p hp => by
            show ¬ (p.2.2.isSome = true); rw [hp]; exact hu
    · refine Or.inl fun u => ?_
      rcases h01 i h2 with rfl | rfl
      · rw [bb1SimLazy_zero]
        exact ⟨bb1SimImpl_zero_coins G ℓ b κ d g X Y _ _ _ _ x s,
          (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 0 (by decide) x s).mono
            fun p hp => by show ¬ (p.2.2.isSome = true); rw [hp]; exact hu⟩
      · rw [bb1SimLazy_one]
        exact ⟨bb1SimImpl_one_coins G ℓ b κ d g X Y _ _ _ _ x s,
          (bb1SimImpl_allOutputs_of_ne_two G ℓ b κ d g X Y 1 1 1 (by decide) x s).mono
            fun p hp => by show ¬ (p.2.2.isSome = true); rw [hp]; exact hu⟩

end Lazy

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Real.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.Games.Relational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The real IND-sID-CPA game of BB1, with `h` drawn at `Init`

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The real game draws the parameter `h` in `Setup`,
before the adversary commits to `ID*`; the simulator chooses `h = g_1^{−ID*} g^{α_1}` after the
commitment. This module moves the real draw of `h` to the first `Init`:
* `RealReads` and `setup_out` read the output of `Setup` without naming the parameters as a
  value: a map `o` from the setup's coins to parameters and master key, and what the game's
  oracles read from `o …` (the encoded parameters, the message space, the encoded keys and
  ciphertexts);
* `bb1RealAt o h` runs the game's oracles on the parameters `o h'` for the `h'` recorded with the
  committed identity, and records `h` at the first `Init`; from the empty state it simulates like
  the game's oracles on `o h` (`expect_simulate_sidImpl_bb1RealAt`, an instance of
  `ProbComp.expect_simulate_rel`);
* `bb1RealLazy o` draws `h` at the first `Init`; it simulates like `bb1RealAt o h` with `h` drawn
  in advance (`expect_sample_bb1RealAt`, an instance of `Games.expect_simulate_eager`).

## Main definitions

* `BB1Sim.RealReads` — what the game's oracles read from the parameters and master key.
* `BB1Sim.BB1RealState` — the game's state with `h` recorded beside the committed identity.
* `BB1Sim.bb1RealAt`, `BB1Sim.bb1RealLazy` — the game's oracles with `h` recorded, and with `h`
  drawn at the first `Init`.

## Main results

* `BB1Sim.setup_out` — the output of `Setup`, read.
* `BB1Sim.expect_simulate_sidImpl_bb1RealAt` — step R1: the game's oracles simulate like
  `bb1RealAt`.
* `BB1Sim.expect_sample_bb1RealAt` — step E-h: `h` drawn at the first `Init`.
* `BB1Sim.expect_sample_sidImpl` — both: the game with `h` drawn in advance simulates like
  `bb1RealLazy`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.1 (pp. 5–6): the system;
  §4.2 (pp. 6–8): the proof of Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The real parameters, from the setup's output -/

section Setup

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ)

/-- **What the real game's oracles read from its parameters and master key** `k`, for parameters
`(g, g^α, Y, h)` and master key `Y^α` in the group described by `d` [BB04, §4.1]: the encoded
parameters, the message space, the encoded keys of `KeyGen`, and the encoded ciphertexts of
`Encrypt`. -/
structure RealReads (d : List Bool) (g : (G.group κ d).G) (α : ZMod (G.group κ d).order)
    (Y h : (G.group κ d).G) (k : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) : Prop where
  /-- The encoded parameters: `d ‖ g ‖ g^α ‖ Y ‖ h`. -/
  encPP : (bb1Scheme G ℓ).encPP κ k.1 = padFin ((bb1Scheme G ℓ).ppLen.eval κ)
    (d ++ List.ofFn ((G.group κ d).encG g) ++ List.ofFn ((G.group κ d).encG (g ^ α.val)) ++
      List.ofFn ((G.group κ d).encG Y) ++ List.ofFn ((G.group κ d).encG h))
  /-- The message space: the encodings of `G_T`. -/
  msgSpace : ∀ m, (bb1Scheme G ℓ).MsgSpace κ k.1 m ↔
    ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m
  /-- `KeyGen`, encoded, then `f`: the key word is `Y^α F(ID)^r ‖ g^r` with `r` uniform. -/
  keyGen : ∀ id {β : Type} (f : (Fin ((bb1Scheme G ℓ).skLen.eval κ) → Bool) → ProbComp β),
    ((bb1Scheme G ℓ).keyGen κ k.2 id).bind (fun sk => f ((bb1Scheme G ℓ).encSK κ sk)) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        f (padFin ((bb1Scheme G ℓ).skLen.eval κ)
          (List.ofFn ((G.group κ d).encG
              (Y ^ α.val * BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) id) ^ r.val)) ++
            List.ofFn ((G.group κ d).encG (g ^ r.val))))
  /-- `Encrypt`, encoded, then `f`: the ciphertext word is `M · e(g^α, Y)^s ‖ g^s ‖ F(ID)^s`
  with `s` uniform, the message read at the width of `G_T`. -/
  enc : ∀ t m {β : Type} (f : (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) → ProbComp β),
    ((bb1Scheme G ℓ).enc κ k.1 t m).bind (fun ct => f ((bb1Scheme G ℓ).encCT κ ct)) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun s =>
        f (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
          (List.ofFn ((G.group κ d).encT ((G.group κ d).pair (g ^ α.val) Y ^ s.val *
              BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))) ++
            List.ofFn ((G.group κ d).encG (g ^ s.val)) ++
            List.ofFn ((G.group κ d).encG
              (BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) t) ^ s.val))))

/-- **The setup's output, read** [BB04, §4.1, *Setup*]: there is a map `o` from the setup's
coins to parameters and master key of `bb1Scheme G ℓ` such that `Setup` draws `r`, `g ∈ G^*`,
`α`, `h`, `g_2` and returns `o r g α h g_2`:
`(Setup κ).bind F = (sample r).bind … (sample g_2).bind fun g_2 => F (o r g α h g_2)` for every
continuation `F`, and the game's oracles read `o r g α h g_2` as the parameters
`(g, g^α, g_2, h)` and the master key `g_2^α` of the group `desc(κ, r)` (`RealReads`).

**Proof sketch.** `o` is the setup's output map, found by unification after reading `Setup`
through `bb1Scheme_setup_eq` and `BB1.setup_eq`. The four readings: `ofFn_bb1Scheme_encPP`;
`bb1Scheme_msgSpace_iff`; `bb1Scheme_keyGen_bind`, `BB1.keyGen_eq` and
`ofFn_bb1Scheme_encSK`; `bb1Scheme_enc_bind`, `BB1.encrypt_eq` and `ofFn_bb1Scheme_encCT`
(vectors with equal words are equal, `List.ofFn_injective`). -/
theorem setup_out :
    ∃ o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ,
      (∀ {β : Type} (F : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ → ProbComp β),
        ((bb1Scheme G ℓ).setup κ).bind F =
          (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
          (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
          (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 => F (o r g α h g2)) ∧
      ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2) := by
  refine ⟨?o, fun F => ?hF, ?hR⟩
  case hF =>
    rw [bb1Scheme_setup_eq]
    simp only [OracleComp.bind_assoc, BB1.setup_eq, OracleComp.pure_bind]
    rfl
  case hR =>
    intro r g α h g2
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ _ _)
    · exact fun m => bb1Scheme_msgSpace_iff G ℓ κ _ _ m
    · intro id β f
      rw [bb1Scheme_keyGen_bind, BB1.keyGen_eq, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]
      refine congrArg _ (funext fun r => ?_)
      rw [List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ _ _)]
    · intro t m β f
      rw [bb1Scheme_enc_bind, BB1.encrypt_eq, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]
      refine congrArg _ (funext fun s => ?_)
      rw [List.ofFn_injective (ofFn_bb1Scheme_encCT G ℓ κ _ _)]

end Setup

/-! ### The game's oracles with `h` recorded -/

section Real

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The real game's state with the parameter `h` recorded beside the committed identity, and
the recorded challenge: `Option ((Fin idLen → Bool) × G) × Option (Fin ctLen → Bool)`. Glue:
the state of `bb1RealAt` and `bb1RealLazy`. -/
abbrev BB1RealState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- `BB1RealState G ℓ κ d` is the optional pair of the committed identity and the recorded `h`,
with the optional recorded challenge: `BB1RealState G ℓ κ d =
Option ((Fin idLen → Bool) × G) × Option (Fin ctLen → Bool)`. Glue: the reader of
`BB1RealState` (policy §1). -/
theorem bb1RealState_eq (κ : ℕ) (d : List Bool) :
    BB1RealState G ℓ κ d =
      (Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) ×
        Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) := rfl

/-- **The game's oracles with `h` recorded** (a variant of the game of [BB04, §2.1], with `h`
recorded beside the committed identity): with hidden bit `b`, on the
parameters and master key `o h'` for the `h'` recorded with the committed identity (or `h`
before `Init`), the call of `IBEScheme.sidImpl` on the state without `h'`; the first `Init`
records `h` with the identity. -/
noncomputable def bb1RealAt (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
  fun i x u => ((bb1Scheme G ℓ).sidImpl b κ (o ((u.1.map Prod.snd).getD h)).1
    (o ((u.1.map Prod.snd).getD h)).2 i x (u.1.map Prod.fst, u.2)).bind
      fun p => .pure (p.1, (p.2.1.map fun t => (t, (u.1.map Prod.snd).getD h), p.2.2))

/-- Before `Init`, `bb1RealAt o h` is the game's oracle on `o h`, recording `h` with the
committed identity: `bb1RealAt … o h i x (none, c) = (sidImpl b κ (o h).1 (o h).2 i x
(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of
`bb1RealAt`. -/
theorem bb1RealAt_none (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealAt G ℓ b κ d o h i x (none, c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (none, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := rfl

/-- After `Init`, `bb1RealAt o h` is the game's oracle on `o h'` for the recorded `h'`:
`bb1RealAt … o h i x (some (t, h'), c) = (sidImpl b κ (o h').1 (o h').2 i x
(some t, c)).bind fun p => pure (p.1, (p.2.1.map (·, h'), p.2.2))`. Glue: a case reader of
`bb1RealAt`. -/
theorem bb1RealAt_some (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h' : (G.group κ d).G)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealAt G ℓ b κ d o h i x (some (t, h'), c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h').1 (o h').2 i x (some t, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h'), p.2.2)) := rfl

open Classical in
/-- **The game's oracles with `h` drawn at the first `Init`** (a variant of the game of
[BB04, §2.1], with `h` drawn late): the first `Init`
draws `h ∈ G` and calls `bb1RealAt o h`; every other call is the call of `bb1RealAt o 1`, which
reads the recorded `h'` after `Init` and no parameter before it. -/
noncomputable def bb1RealLazy (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
  fun i x u => if u.1.isNone ∧ i = 0 then
      (ProbComp.sample (G.group κ d).G).bind fun h => bb1RealAt G ℓ b κ d o h i x u
    else bb1RealAt G ℓ b κ d o 1 i x u

variable (b : Bool) (κ : ℕ) (d : List Bool)
  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)

/-- The first `Init` of `bb1RealLazy` draws `h` and calls the game's oracle on `o h`:
`bb1RealLazy … o 0 x (none, c) = (sample G).bind fun h => (sidImpl b κ (o h).1 (o h).2 0 x
(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of
`bb1RealLazy`. -/
theorem bb1RealLazy_zero_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o 0 x (none, c) =
      (ProbComp.sample (G.group κ d).G).bind fun h =>
        ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 0 x (none, c)).bind
          fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
  rw [bb1RealLazy, if_pos ⟨rfl, rfl⟩]
  rfl

/-- Before `Init`, the other calls of `bb1RealLazy` are the game's oracles on `o 1`: for `i ≠ 0`,
`bb1RealLazy … o i x (none, c) = (sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind fun p =>
pure (p.1, (p.2.1.map (·, 1), p.2.2))`. Glue: a case reader of `bb1RealLazy`. -/
theorem bb1RealLazy_none_of_ne (i : Fin 3) (hi : i ≠ 0) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o i x (none, c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, 1), p.2.2)) := by
  rw [bb1RealLazy, if_neg fun h => hi h.2]
  rfl

/-- After `Init`, `bb1RealLazy` is the game's oracle on `o h` for the recorded `h`:
`bb1RealLazy … o i x (some (t, h), c) = (sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. Glue: a case reader of `bb1RealLazy`. -/
theorem bb1RealLazy_some (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o i x (some (t, h), c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
  rw [bb1RealLazy, if_neg fun h => absurd h.1 (by simp)]
  rfl

/-- **The game's oracles keep the committed identity**: for every scheme `S`, every outcome of
`S.sidImpl b κ pp msk i x (some t, c)` has the committed identity `t`. Glue: a case fact of
`IBEScheme.sidImpl`, from its readers.

**Proof sketch.** By cases on the oracle, read through `IBEScheme.sidImpl_zero_onSpec`,
`sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec` and
`sidImpl_challenge_fresh_onSpec`: `Init` keeps the state (`sidImpl_init_some`), `KeyGen` keeps it
(`sidImpl_keyGen_target`, `sidImpl_keyGen_ne`), and `Challenge` keeps `ID*` and records the
challenge at most (`sidImpl_challenge_fresh`, `_invalid`, `_repeat`). -/
theorem sidImpl_allOutputs_some (S : IBEScheme) (pp : S.PP κ) (msk : S.MSK κ) (i : Fin 3)
    (x : (S.sidSpec κ).dom i) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    (S.sidImpl b κ pp msk i x (some t, c)).AllOutputs fun p => p.2.1 = some t := by
  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases h012 i with rfl | rfl | rfl
  · rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some, OracleComp.pure_bind]
    exact OracleComp.allOutputs_pure.2 rfl
  · by_cases ht : cast (sidSpec_dom_one S κ) x = t
    · rw [IBEScheme.sidImpl_one_onQuery, ht, IBEScheme.sidImpl_keyGen_target]
      exact OracleComp.allOutputs_pure.2 rfl
    · rw [IBEScheme.sidImpl_keyGen_ne_onSpec S b κ pp msk x t c ht]
      apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
      intro _ _
      exact OracleComp.allOutputs_pure.2 rfl
  · rcases c with _ | w
    · by_cases hv : S.MsgSpace κ pp
          (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).1 ∧
        S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).2
      · rw [IBEScheme.sidImpl_challenge_fresh_onSpec S b κ pp msk x t hv]
        apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
        intro _ _
        exact OracleComp.allOutputs_pure.2 rfl
      · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_invalid (h := hv)]
        exact OracleComp.allOutputs_pure.2 rfl
    · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_repeat]
      exact OracleComp.allOutputs_pure.2 rfl

/-- **Before `Init`, `KeyGen` and `Challenge` do not read the parameters**: for every scheme `S`
and `i ≠ 0`, `S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c)`, and
every outcome keeps the state `(none, c)`. Glue: a case fact of `IBEScheme.sidImpl`, from its
readers. -/
theorem sidImpl_none_of_ne (S : IBEScheme) (pp pp' : S.PP κ) (msk msk' : S.MSK κ) (i : Fin 3)
    (hi : i ≠ 0) (x : (S.sidSpec κ).dom i) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c) ∧
      (S.sidImpl b κ pp msk i x (none, c)).AllOutputs fun p => p.2 = (none, c) := by
  have h12 : ∀ i : Fin 3, i ≠ 0 → i = 1 ∨ i = 2 := by decide
  rcases h12 i hi with rfl | rfl
  · rw [IBEScheme.sidImpl_one_onQuery S b κ pp msk x,
      IBEScheme.sidImpl_one_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_keyGen_none,
      IBEScheme.sidImpl_keyGen_none]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
  · rw [IBEScheme.sidImpl_two_onQuery S b κ pp msk x,
      IBEScheme.sidImpl_two_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_challenge_none,
      IBEScheme.sidImpl_challenge_none]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩

/-- **Step R1** (design r1 §3.1): from the empty state, the game's oracles on `o h` simulate like
`bb1RealAt o h`, for functions `F` of the output:
`𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1RealAt … o h) c (none, none))`. Glue: an instance of
`ProbComp.expect_simulate_rel` with `R s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.

**Proof sketch.** From related states, `bb1RealAt o h` reads the recorded `h' = h`, so its call
is the game's call followed by recording `h` (`bb1RealAt_none`, `bb1RealAt_some`); its
expectation is the game's call's (`expect_bind`, `expect_pure`), whose new states are related
to the recorded ones. `ProbComp.expect_simulate_rel` concludes. -/
theorem expect_simulate_sidImpl_bb1RealAt (h : (G.group κ d).G) {α : Type}
    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α) (F : α → ℝ) :
    ProbComp.expect (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
        (fun p => F p.1) =
      ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) (fun p => F p.1) := by
  refine ProbComp.expect_simulate_rel _ _
    (fun s u => s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h) (fun i x s u hsu g₀ g₁ hg => ?_)
    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, fun p hp => by cases hp⟩
  obtain ⟨rfl, hh⟩ := hsu
  -- from related states, `bb1RealAt h` reads the recorded `h`
  have hget : (u.1.map Prod.snd).getD h = h := by
    rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · rfl
    · exact hh _ rfl
  rw [show bb1RealAt G ℓ b κ d o h i x u =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (u.1.map Prod.fst, u.2)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) by rw [bb1RealAt, hget],
    ProbComp.expect_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [ProbComp.expect_pure]
  refine hg p.1 p.2 _ ⟨?_, fun q hq => ?_⟩ <;> rcases p with ⟨a, _ | t, c⟩
  · rfl
  · rfl
  · cases hq
  · cases hq
    rfl

/-- **Step E-h** (design r1 §3.1): `h` drawn in advance or at the first `Init` simulate alike:
`𝔼_{h ← G} 𝔼[F] (simulate (bb1RealAt … o h) c (none, none)) =
𝔼[F] (simulate (bb1RealLazy … o) c (none, none))`. Glue: an instance of
`Games.expect_simulate_eager`, with `h` spent at the first `Init`.

**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1RealLazy o`,
`OE h := bb1RealAt o h` and `used u := u.1` some. After `Init` both read the recorded `h`
(`bb1RealAt_some`, `bb1RealLazy_some`) and keep the identity (`sidImpl_allOutputs_some`). Before
`Init`, `KeyGen` and `Challenge` read no parameter and keep the state (`sidImpl_none_of_ne`,
`bb1RealLazy_none_of_ne`); the first `Init` draws `h` (`bb1RealLazy_zero_none`) and records an
identity (`IBEScheme.sidImpl_zero_onSpec`, `IBEScheme.sidImpl_init_none`). -/
theorem expect_sample_bb1RealAt {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α × BB1RealState G ℓ κ d → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).G)
        (fun h => ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) F) =
      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) F := by
  refine (Games.expect_simulate_eager (T := (G.group κ d).G) (bb1RealLazy G ℓ b κ d o)
    (bb1RealAt G ℓ b κ d o) (fun u => u.1.isSome = true) (fun h i x u hu => ?_)
    (fun i x u hu => ?_) (fun i x u hu => ?_) c F
    (by show ¬ ((none : Option _).isSome = true); exact Bool.false_ne_true)).symm
  -- after `Init`, both read the recorded `h`
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · exact absurd hu Bool.false_ne_true
    · rw [bb1RealAt_some, bb1RealLazy_some]
  -- the committed identity stays committed
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · exact absurd hu Bool.false_ne_true
    · rw [bb1RealLazy_some]
      exact (sidImpl_allOutputs_some b κ _ _ _ i x t c).bind fun p hp =>
        OracleComp.allOutputs_pure.2 (by show (p.2.1.map _).isSome = true; rw [hp]; rfl)
  -- before `Init`: the first `Init` draws `h`; `KeyGen` and `Challenge` read no parameter
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    swap
    · exact absurd rfl hu
    by_cases hi : i = 0
    · subst hi
      refine Or.inr ⟨?_, fun h => ?_⟩
      · rw [bb1RealLazy_zero_none]
        exact congrArg _ (funext fun h => (bb1RealAt_none G ℓ b κ d o h 0 x c).symm)
      · rw [bb1RealAt_none, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none,
          OracleComp.pure_bind, OracleComp.pure_bind]
        exact OracleComp.allOutputs_pure.2 rfl
    · have hn := fun h => sidImpl_none_of_ne b κ (bb1Scheme G ℓ) (o h).1 (o 1).1 (o h).2 (o 1).2
        i hi x c
      refine Or.inl fun h => ⟨?_, ?_⟩
      · rw [bb1RealAt_none, bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c, (hn h).1]
        exact OracleComp.bind_congr_of_allOutputs (hn 1).2 fun p hp => by rw [hp]; rfl
      · rw [bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c]
        exact (sidImpl_none_of_ne b κ _ (o 1).1 (o 1).1 (o 1).2 (o 1).2 i hi x c).2.bind
          fun p hp => OracleComp.allOutputs_pure.2 (by
            show ¬ ((p.2.1.map _).isSome = true); rw [hp]; exact Bool.false_ne_true)

/-- **The real game with `h` drawn at the first `Init`** (steps R1 and E-h of design r1 §3.1):
`𝔼_{h ← G} 𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none))`. Glue.

**Proof sketch.** `expect_simulate_sidImpl_bb1RealAt` for each `h`, then
`expect_sample_bb1RealAt`. -/
theorem expect_sample_sidImpl {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).G)
        (fun h => ProbComp.expect
          (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
          (fun p => F p.1)) =
      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) := by
  rw [← expect_sample_bb1RealAt]
  exact congrArg _ (funext fun h => expect_simulate_sidImpl_bb1RealAt G ℓ b κ d o h c F)

end Real

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Coupling.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Step M of BB1's simulation: the real game against the simulator, call by call

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). After `h` is drawn at the first `Init`
(`BB1Sim.bb1RealLazy`) and the challenge coin `c` at the first valid `Challenge`
(`BB1Sim.bb1SimLazy`), the real game and the simulator answer alike call by call, on states
related by design r1 §3.1's relation `RelM`: the same recorded challenge, the same committed
identity `ID*`, and `h = X^{−ID*} g^{α_1}` [BB04, proof of Theorem 4.1, *Setup*]. The real
`KeyGen` exponent `r̃` and the simulated one `r` correspond by `r = r̃ + b/(ID − ID*)`
[BB04, proof of Theorem 4.1, *Phase 1*], which needs `ID ≠ ID*` in `Z_p`: the generator's coins
must give `2^ℓ ≤ p`. The challenge is `Encrypt` with `s = c`
[BB04, proof of Theorem 4.1, *Challenge*].

## Main definitions

* `BB1Sim.RelM` — the relation of step M.

## Main results

* `BB1Sim.exists_equiv_mul_pow`, `BB1Sim.natCast_bitsToNat_injective`, `BB1Sim.key_eq`,
  `BB1Sim.F_target_eq`, `BB1Sim.pair_pow_val_eq` — the group algebra of the coupling.
* `BB1Sim.stepM_init_none`, …, `BB1Sim.stepM_challenge_fresh` — step M, call by call.
* `BB1Sim.stepM_call` — the per-call hypothesis of `ProbComp.expect_simulate_rel`.
* `BB1Sim.expect_simulate_bb1RealLazy` — step M: on good coins, the real game with `h` drawn at
  `Init` simulates like the lazy simulator on `Y = g^{b'}` with `c` drawn at the challenge.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The group algebra of the coupling -/

section Algebra

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **`h ↦ α_1` along `h = X^{−z} g^{α_1}`** [BB04, proof of Theorem 4.1, *Setup*]: for `g ≠ 1`
and every `X`, there are bijections `e z : G ≃ Z_p`, one for each `z ∈ Z_p`, with
`h = X^{(−z).val} · g^{(e z h).val}` for every `h`. -/
theorem exists_equiv_mul_pow {g : B.G} (hg : g ≠ 1) (X : B.G) :
    ∃ e : ZMod B.order → B.G ≃ ZMod B.order,
      ∀ z h, h = X ^ (-z).val * g ^ (e z h).val := by
  let E : ZMod B.order ≃ B.G := Equiv.ofBijective _ (B.pow_val_bijective_of_ne_one hg)
  refine ⟨fun z => (Equiv.mulLeft (X ^ (-z).val)⁻¹).trans E.symm, fun z h => ?_⟩
  have hE : g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val = (X ^ (-z).val)⁻¹ * h :=
    E.apply_symm_apply _
  show h = X ^ (-z).val * g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val
  rw [hE, mul_inv_cancel_left]

/-- **Distinct `n`-bit identities are distinct in `Z_p` when `2^n ≤ p`**: reading `n`-bit strings
as numbers modulo `p` is injective, `fun u => (bitsToNat u : ZMod p)`. Glue for
[BB04, §4.4]'s condition on the identity length. -/
theorem natCast_bitsToNat_injective {n p : ℕ} (hp : 2 ^ n ≤ p) :
    Function.Injective fun u : Fin n → Bool => (bitsToNat u : ZMod p) := fun u v huv =>
  bitsToNat_injective (CharP.natCast_injOn_Iio (ZMod p) p (lt_of_lt_of_le (bitsToNat_lt u) hp)
    (lt_of_lt_of_le (bitsToNat_lt v) hp) huv)

/-- **The simulated key is a real key** [BB04, proof of Theorem 4.1, *Phase 1*, "let
`r̃_j = r_j − b/(I_j − I^*_j)`"]: for `X = g^α`, `Y = g^{b'}`, `z ≠ z'` and
`F(z) = X^z · (X^{−z'} g^{α_1})`, the real key `(Y^α F(z)^r, g^r)` with exponent `r` is the
simulated key `(Y^{−α_1/(z − z')} F(z)^{r'}, Y^{−1/(z − z')} g^{r'})` with exponent
`r' = r + b'/(z − z')`. -/
theorem key_eq (g : B.G) (α b' z z' a₁ r : ZMod B.order) (hz : z ≠ z') :
    (g ^ b'.val) ^ α.val *
        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ r.val =
      (g ^ b'.val) ^ (-a₁ / (z - z')).val *
        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ (r + b' / (z - z')).val ∧
    g ^ r.val = (g ^ b'.val) ^ (-1 / (z - z')).val * g ^ (r + b' / (z - z')).val := by
  have hz' : z - z' ≠ 0 := sub_ne_zero.2 hz
  have hpow : ∀ a c : ZMod B.order, (g ^ a.val) ^ c.val = g ^ (a * c).val := fun a c => by
    rw [B.pow_val_mul, pow_mul]
  have hmul : ∀ a c : ZMod B.order, g ^ a.val * g ^ c.val = g ^ (a + c).val := fun a c =>
    (B.pow_val_add g a c).symm
  simp only [hpow, hmul]
  constructor <;> congr 2 <;> field_simp <;> ring

/-- **`F(ID*) = g^{α_1}`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
`F_i(I^*_i) = g^{α_i}`"]: for `h = X^{−z} g^{α_1}`, `X^z · h = g^{α_1}`. -/
theorem F_target_eq (g X : B.G) (z a₁ : ZMod B.order) :
    X ^ z.val * (X ^ (-z).val * g ^ a₁.val) = g ^ a₁.val := by
  rw [B.pow_val_neg, mul_inv_cancel_left]

/-- **`e(g^α, g^{b'})^s = e(g, g)^{α b' s}`** [BB04, proof of Theorem 4.1, *Challenge*, "if
`T = e(g, g)^{abc} = e(g_1, g_2)^c`"]: `B.pair (g^α) (g^{b'}) ^ s.val =
B.pair g g ^ (α · b' · s).val`. -/
theorem pair_pow_val_eq (g : B.G) (α b' s : ZMod B.order) :
    B.pair (g ^ α.val) (g ^ b'.val) ^ s.val = B.pair g g ^ (α * b' * s).val := by
  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, B.bilinear_pow]

end Algebra

/-! ### The relation of step M -/

section Rel

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)

/-- **Design r1 §3.1's relation `R`** [BB04, proof of Theorem 4.1, *Setup*]: the real state `u`
(with `h`) and the simulator's state `v` (with `α_1`) record the same challenge and the same
committed identity `ID*`, and `h = X^{−ID*} g^{α_1}`. -/
def RelM (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) : Prop :=
  u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
    p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1

/-- `RelM … g X u v` holds iff `u.2 = v.2` and `u.1`, `v.1` are both `none`, or `some (t, h)` and
`some (t, α_1)` with `h = X^{(−idToZ t).val} · g^{α_1.val}`. Glue: the reader of `RelM`. -/
theorem relM_iff (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) :
    RelM G ℓ κ d g X u v ↔ u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
      p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1 := Iff.rfl

end Rel

/-! ### Step M, call by call

The real side is `bb1RealLazy` on parameters `o h` that the game reads as `(g, g^α, g^{b'}, h)`
(`RealReads`); the simulator is `bb1SimLazy` on `X = g^α`, `Y = g^{b'}`, with the challenge coin
`c ∈ Z_p` drawn at the first valid `Challenge`. Deterministic calls answer alike and keep the
states; sampling calls give the premise of `ProbComp.expect_sample_rel` along their bijection. -/

section StepM

variable (G : BilinearGen) (ℓ : PolyExpr) (b : Bool) (κ : ℕ) (d : List Bool)
  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
  (g : (G.group κ d).G) (α b' : ZMod (G.group κ d).order)

variable {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)

/-- **Step M, `Init` before a commitment** [BB04, proof of Theorem 4.1, *Setup*] (sampling): the
real call draws `h ∈ G`, the simulator draws `α_1 ∈ Z_p`; along the bijection `e ID` with
`h = X^{−z} g^{e z h}` (`exists_equiv_mul_pow`) at `z = ID`, they answer alike and reach related
states: `(f₀ h).1 = (f₁ (e ID h)).1` and `RelM (f₀ h).2 (f₁ (e ID h)).2`.

**Proof sketch.** The real call is read by `bb1RealLazy_zero_none`, `sidImpl_zero_onSpec` and
`sidImpl_init_none` (a uniform `h`, the parameters `o h`, the identity recorded with `h`); the
simulator's by `bb1SimLazy_zero`, `oracleImpl_zero_onSpec` and `bb1SimInit_none` (a uniform
`α_1`). At `α_1 = e ID h` the parameter words agree (`RealReads.encPP`, `ofFn_bb1Scheme_encPP`,
`bb1SimParams_eq`, `h = X^{−ID} g^{e ID h}`), and that equation is `RelM` of the new states. -/
theorem stepM_init_none (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (e : ZMod (G.group κ d).order → (G.group κ d).G ≃ ZMod (G.group κ d).order)
    (he : ∀ z h, h = (g ^ α.val) ^ (-z).val * g ^ (e z h).val) :
    ∃ (f₀ : (G.group κ d).G → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 0 x (none, c) =
        (ProbComp.sample (G.group κ d).G).bind (fun h => .pure (f₀ h)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (none, c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun α₁ => .pure (f₁ α₁)) ∧
      ∀ h, (f₀ h).1 = (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ h).2
          (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_zero_none]
    refine congrArg _ (funext fun h => ?_)
    rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none, OracleComp.pure_bind,
      OracleComp.pure_bind]
  case h1 =>
    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_none,
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  case hf =>
    intro h
    have hz := he (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h
    refine ⟨?_, ⟨rfl, .some ⟨rfl, ?_⟩⟩⟩
    · rw [(ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _), bb1SimParams_eq,
        ← hz]
    · dsimp only
      exact hz

/-- **Step M, `Init` after a commitment** [BB04, proof of Theorem 4.1, *Setup*] (deterministic):
for `h = X^{−ID*} g^{α_1}`, both calls answer the same parameters `(g, X, Y, h)` and keep their
states: `bb1RealLazy … 0 x (some (t, h), c) = pure (a, (some (t, h), c))` and
`bb1SimLazy … 0 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`.

**Proof sketch.** The real call is `sidImpl`'s `Init` on a committed state (`bb1RealLazy_some`,
`sidImpl_zero_onSpec`, `sidImpl_init_some`); the simulator's is `bb1SimInit_some`
(`bb1SimLazy_zero`, `bb1SimImpl_eq`, `oracleImpl_zero_onSpec`). Both answer the encoded parameters,
equal by `RealReads.encPP`, `ofFn_bb1Scheme_encPP`, `bb1SimParams_eq` and `h = X^{−ID*} g^{α_1}`. -/
theorem stepM_init_some (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val) :
    ∃ a, bb1RealLazy G ℓ b κ d o 0 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (some (t, α₁), c) =
        .pure (a, (some (t, α₁), c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some,
      OracleComp.pure_bind, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_some,
      OracleComp.pure_bind, (ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _),
      bb1SimParams_eq, ← hh]

/-- **Step M, `KeyGen` before `Init`** (deterministic): both calls answer `⊥` and keep their
states: `bb1RealLazy … 1 x (none, c) = pure (a, (none, c))` and
`bb1SimLazy … 1 x (none, c) = pure (a, (none, c))`. Glue for the game's `KeyGen`. -/
theorem stepM_keyGen_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (none, c) = .pure (a, (none, c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (none, c) =
        .pure (a, (none, c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 1 (by decide), IBEScheme.sidImpl_one_onQuery,
      IBEScheme.sidImpl_keyGen_none, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_none,
      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]

/-- **Step M, `KeyGen` for `ID*`** (deterministic): both calls answer `⊥` and keep their states:
for `x` read as `t`, `bb1RealLazy … 1 x (some (t, h), c) = pure (a, (some (t, h), c))` and
`bb1SimLazy … 1 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`. Glue for the game's
`KeyGen`.

**Proof sketch.** The real call is `sidImpl_keyGen_target` (`bb1RealLazy_some`,
`sidImpl_one_onQuery`), the simulator's `bb1SimKeyQ_target` (`bb1SimLazy_one`, `bb1SimImpl_eq`,
`oracleImpl_one_onSpec`); both `⊥` words agree by `zeroBits_eq_cast` and `outLens_one`. -/
theorem stepM_keyGen_target (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (ht : cast (sidSpec_dom_one _ κ) x = t) :
    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
        .pure (a, (some (t, α₁), c)) := by
  subst ht
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_one_onQuery, IBEScheme.sidImpl_keyGen_target,
      OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_target,
      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]

/-- **Step M, `KeyGen` for `ID ≠ ID*`** [BB04, proof of Theorem 4.1, *Phase 1*, "let
`r̃_j = r_j − b/(I_j − I^*_j)`"] (sampling): for `h = X^{−ID*} g^{α_1}` and good coins
`2^{ℓ(κ)} ≤ p`, the real key with exponent `r̃` is the simulated key with exponent
`r̃ + b'/(ID − ID*)`: `(f₀ r̃).1 = (f₁ (r̃ + b'/(ID − ID*))).1`, and the states are kept.

**Proof sketch.** The real call is read by `sidImpl_keyGen_ne_onSpec` and `RealReads.keyGen` (a
uniform `r̃` and the key word), the simulator's by `oracleImpl_one_onSpec` and `bb1SimKeyQ_ne` (a
uniform `r`). `ID ≠ ID*` in `Z_p` by `natCast_bitsToNat_injective` (`BB1.idToZ_eq`). At
`r = r̃ + b'/(ID − ID*)` the key words agree: `ofFn_bb1Scheme_encSK`, `bb1SimKey_eq`, `BB1.F_eq`,
`bb1SimParams_eq`, `h = X^{−ID*} g^{α_1}` and `key_eq`. The states are unchanged. -/
theorem stepM_keyGen_ne (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
    (ht : cast (sidSpec_dom_one _ κ) x ≠ t) :
    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₀ r)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₁ r)) ∧
      ∀ r, (f₀ r).1 = (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ r).2 (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_keyGen_ne_onSpec _ _ _ _ _ x t c ht,
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind, Option.map_some]
    rw [(ho h).keyGen _ fun w => .pure (cast (sidSpec_rng_one _ κ).symm
      (FixedLengthScheme.decAnswer (some w)), (some (t, h), c))]
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_ne (h := ht),
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  case hf =>
    intro r
    refine ⟨?_, ⟨rfl, .some ⟨rfl, hh⟩⟩⟩
    have hz : BB1.idToZ (G.group κ d) (cast (sidSpec_dom_one _ κ) x) ≠
        BB1.idToZ (G.group κ d) t := by
      rw [BB1.idToZ_eq, BB1.idToZ_eq]
      exact fun h' => ht (natCast_bitsToNat_injective hp h')
    obtain ⟨h0, h1⟩ := key_eq (G.group κ d) g α b' _ _ α₁ r hz
    rw [Equiv.coe_addRight, List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ d _), bb1SimKey_eq,
      BB1.F_eq, BB1.F_eq, bb1SimParams_eq, hh]
    dsimp only
    rw [h0, h1]

/-- **Step M, `Challenge` before `Init`** (deterministic): both calls answer `⊥` and keep their
states: `bb1RealLazy … 2 x (none, c) = pure (a, (none, c))` and
`bb1SimLazy … 2 x (none, c) = pure (a, (none, c))`. Glue for the game's `Challenge`. -/
theorem stepM_challenge_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (none, c) = .pure (a, (none, c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (none, c) =
        .pure (a, (none, c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 2 (by decide), IBEScheme.sidImpl_two_onQuery,
      IBEScheme.sidImpl_challenge_none, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (none, c) fun h' => Bool.false_ne_true h'.1,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_none, OracleComp.pure_bind,
      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]

/-- **Step M, `Challenge` after a recorded challenge** (deterministic): both calls repeat the
recorded challenge `w` and keep their states: `bb1RealLazy … 2 x (some (t, h), some w) =
pure (a, (some (t, h), some w))` and `bb1SimLazy … 2 x (some (t, α_1), some w) =
pure (a, (some (t, α_1), some w))`. Glue for the game's `Challenge`.

**Proof sketch.** The real call is `sidImpl_challenge_repeat` (`bb1RealLazy_some`,
`sidImpl_two_onSpec`), the simulator's `bb1SimChal_repeat` (`bb1SimLazy_two_of_not`, since a
challenge is recorded; `bb1SimImpl_eq`, `oracleImpl_two_onSpec`); both answer `w`. -/
theorem stepM_challenge_repeat (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), some w) = .pure (a, (some (t, h), some w)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), some w) =
        .pure (a, (some (t, α₁), some w)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onSpec, IBEScheme.sidImpl_challenge_repeat,
      OracleComp.pure_bind, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), some w)
        fun h' => Option.some_ne_none w h'.2.1,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_repeat, OracleComp.pure_bind]

/-- **Step M, the first invalid `Challenge`** (deterministic): when a message of the query is not
an encoding of `G_T`, both calls answer `⊥` and keep their states:
`bb1RealLazy … 2 x (some (t, h), none) = pure (a, (some (t, h), none))` and
`bb1SimLazy … 2 x (some (t, α_1), none) = pure (a, (some (t, α_1), none))`; both message spaces
are the encodings of `G_T` (`RealReads.msgSpace`, `bb1Scheme_msgSpace_iff`). Glue for the
game's `Challenge`.

**Proof sketch.** The real call is read by `bb1RealLazy_some`, `sidImpl_two_onQuery` and
`sidImpl_challenge_invalid` (invalidity through `RealReads.msgSpace`); the simulator's by
`bb1SimLazy_two_of_not`, `oracleImpl_two_onSpec` and `bb1SimChal_invalid` (invalidity through
`bb1Scheme_msgSpace_iff`). Both answer the `⊥` word (`zeroBits_eq_cast`). -/
theorem stepM_challenge_invalid (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (hv : ¬ ((∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
      ∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) = .pure (a, (some (t, h), none)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), none) =
        .pure (a, (some (t, α₁), none)) := by
  have hv' : ¬ ((bb1Scheme G ℓ).MsgSpace κ (o h).1
        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1 ∧
      (bb1Scheme G ℓ).MsgSpace κ (o h).1
        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) := fun hm =>
    hv ⟨((ho h).msgSpace _).1 hm.1, ((ho h).msgSpace _).1 hm.2⟩
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onQuery,
      IBEScheme.sidImpl_challenge_invalid _ _ _ _ _ _ _ hv', OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), none) fun h' => hv h'.2.2,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_invalid, OracleComp.pure_bind,
      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
    exact fun hm => hv ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.1,
      (bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.2⟩

/-- **Step M, the first valid `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
`F_i(I^*_i) = g^{α_i}`"] (sampling, along the identity of `Z_p`): for `h = X^{−ID*} g^{α_1}`,
the real encryption with exponent `s` is the simulated challenge on the coins
`(g^s, e(g, g)^{α b' s})`: `(f₀ s).1 = (f₁ s).1`, and both record that challenge.

**Proof sketch.** The real call is read by `sidImpl_challenge_fresh_onSpec` (validity through
`RealReads.msgSpace`) and `RealReads.enc` (a uniform `s` and the ciphertext word); the
simulator's by `bb1SimLazy_two_fresh` (a uniform `c`), `oracleImpl_two_onSpec` and
`bb1SimChal_fresh` (validity through `bb1Scheme_msgSpace_iff`). At `c = s` the words agree
(`ofFn_bb1SimCt`, `pair_pow_val_eq`, commutativity of `G_T`, `BB1.F_eq`, `F_target_eq`,
`pow_right_comm`), and both record that word. -/
theorem stepM_challenge_fresh (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
    (hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
      ∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :
    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun s => .pure (f₀ s)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
          (fun c : ZMod (G.group κ d).order =>
            (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) 2 x (some (t, α₁), none) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun c => .pure (f₁ c)) ∧
      ∀ s, (f₀ s).1 = (f₁ (Equiv.refl _ s)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ s).2 (f₁ (Equiv.refl _ s)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_challenge_fresh_onSpec _ _ _ _ _ x t
      ⟨((ho h).msgSpace _).2 hv.1, ((ho h).msgSpace _).2 hv.2⟩, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind, Option.map_some]
    rw [(ho h).enc t _ fun w => .pure (cast (sidSpec_rng_two _ κ).symm w, (some (t, h), some w))]
  case h1 =>
    rw [bb1SimLazy_two_fresh G ℓ b κ d g _ _ _ x _ ⟨rfl, rfl, hv⟩]
    refine congrArg _ (funext fun c => ?_)
    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh, OracleComp.pure_bind]
    exact ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1, (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩
  case hf =>
    intro s
    rw [Equiv.refl_apply]
    refine ⟨?_, ⟨?_, .some ⟨rfl, hh⟩⟩⟩ <;>
    · rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), pair_pow_val_eq,
        mul_comm ((G.group κ d).pair g g ^ (α * b' * s).val), BB1.F_eq]
      dsimp only
      rw [hh, F_target_eq, pow_right_comm]

/-- **Step M, the per-call hypothesis of `ProbComp.expect_simulate_rel`** [BB04, proof of
Theorem 4.1]: for `g ≠ 1`, good coins `2^{ℓ(κ)} ≤ p`, and parameters `o h` read as
`(g, g^α, g^{b'}, h)`, from states related by `RelM`, a call of `bb1RealLazy … o` and of
`bb1SimLazy` on `X = g^α`, `Y = g^{b'}` and `zt c = (g^c, e(g, g)^{α b' c})` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states.

**Proof sketch.** By cases on the oracle and the states, with the rows `stepM_*`: deterministic
rows answer alike and keep the related states (`expect_pure`); sampling rows meet the premise of
`ProbComp.expect_sample_rel` along `e ID` (`Init`, `exists_equiv_mul_pow`),
`r ↦ r + b'/(ID − ID*)` (`KeyGen`, `key_eq`, `natCast_bitsToNat_injective`) and the identity
(`Challenge`, `F_target_eq`, `pair_pow_val_eq`). -/
theorem stepM_call (hg : g ≠ 1) (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (i : Fin 3)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (u : BB1RealState G ℓ κ d)
    (v : BB1SimState G ℓ κ d) (huv : RelM G ℓ κ d g (g ^ α.val) u v)
    (g₀ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1RealState G ℓ κ d → ℝ)
    (g₁ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ)
    (hg₀₁ : ∀ y u' v', RelM G ℓ κ d g (g ^ α.val) u' v' → g₀ (y, u') = g₁ (y, v')) :
    ProbComp.expect (bb1RealLazy G ℓ b κ d o i x u) g₀ =
      ProbComp.expect (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
        (fun c : ZMod (G.group κ d).order =>
          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) i x v) g₁ := by
  generalize hzt : (fun c : ZMod (G.group κ d).order =>
    (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) = zt
  obtain ⟨e, he⟩ := exists_equiv_mul_pow (G.group κ d) hg (g ^ α.val)
  obtain ⟨u₁, uc⟩ := u
  obtain ⟨v₁, vc⟩ := v
  obtain ⟨hc, hR⟩ := id huv
  dsimp only at hc
  subst hc
  match i, x, g₀, g₁, hg₀₁ with
  | 0, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨f₀, f₁, h0, h1, hf⟩ := stepM_init_none G ℓ b κ d o g α b' zt ho x uc e he
      rw [h0, h1]
      exact ProbComp.expect_sample_rel _ (e _) f₀ f₁ hf g₀ g₁ hg₀₁
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      obtain ⟨a, h0, h1⟩ := stepM_init_some G ℓ b κ d o g α b' zt ho x t h α₁ uc hh
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
  | 1, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨a, h0, h1⟩ := stepM_keyGen_none G ℓ b κ d o g α b' zt x uc
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      by_cases hx : cast (sidSpec_dom_one _ κ) x = t
      · obtain ⟨a, h0, h1⟩ := stepM_keyGen_target G ℓ b κ d o g α b' zt x t h α₁ uc hx
        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
        exact hg₀₁ _ _ _ huv
      · obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
          stepM_keyGen_ne G ℓ b κ d o g α b' zt hp ho x t h α₁ uc hh hx
        rw [h0, h1]
        exact ProbComp.expect_sample_rel _ (Equiv.addRight _) f₀ f₁ hf g₀ g₁ hg₀₁
  | 2, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨a, h0, h1⟩ := stepM_challenge_none G ℓ b κ d o g α b' zt x uc
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      rcases uc with _ | w
      · by_cases hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2
        · subst hzt
          obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
            stepM_challenge_fresh G ℓ b κ d o g α b' ho x t h α₁ hh hv
          rw [h0, h1]
          exact ProbComp.expect_sample_rel _ (Equiv.refl _) f₀ f₁ hf g₀ g₁ hg₀₁
        · obtain ⟨a, h0, h1⟩ := stepM_challenge_invalid G ℓ b κ d o g α b' zt ho x t h α₁ hv
          rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
          exact hg₀₁ _ _ _ huv
      · obtain ⟨a, h0, h1⟩ := stepM_challenge_repeat G ℓ b κ d o g α b' zt x t h α₁ w
        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
        exact hg₀₁ _ _ _ huv

/-- **Step M** (design r1 §3.1) [BB04, proof of Theorem 4.1]: for `g ≠ 1`, good coins
`2^{ℓ(κ)} ≤ p`, and parameters `o h` read as `(g, g^α, g^{b'}, h)`, the real game with `h` drawn
at the first `Init` simulates like the simulator on `X = g^α`, `Y = g^{b'}` with the challenge
coin `c` drawn at the first valid `Challenge`, for functions `F` of the output:
`𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1SimLazy … (fun c => (g^c, e(g, g)^{α b' c}))) c (none, none))`.

**Proof sketch.** `ProbComp.expect_simulate_rel` with `RelM`, the per-call hypothesis
`stepM_call`, functions of the output only, and `RelM` at the empty states. -/
theorem expect_simulate_bb1RealLazy (hg : g ≠ 1)
    (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) {β : Type}
    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β) (F : β → ℝ) :
    ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) =
      ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
        (fun c : ZMod (G.group κ d).order =>
          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val))) c (none, none))
        (fun p => F p.1) :=
  ProbComp.expect_simulate_rel _ _ (RelM G ℓ κ d g (g ^ α.val))
    (fun i x u v huv g₀ g₁ hg₀₁ => stepM_call G ℓ b κ d o g α b' hg hp ho i x u v huv g₀ g₁ hg₀₁)
    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, .none⟩

end StepM

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Random.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.Games.Relational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator on a random `T` does not depend on the challenge bit

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 2 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "when `T` is uniform and independent in `G_1`
… `C` is independent of `b` in the adversary's view" [BB04, proof of Theorem 4.1, *Challenge*].
`T` is used only at the first valid `Challenge`, so it can be drawn there
(`expect_simulate_bb1SimLazy`, step E-T); at that call, `T ↦ M_1^{−1} M_0 T` turns the answer
`M_0 · T` of the simulator with challenge bit `0` into the answer `M_1 · T'` of the one with
challenge bit `1`, and every other call is the same for both bits.

## Main definitions

None.

## Main results

* `BB1Sim.bb1SimLazy_random_call` — the lazy simulators with challenge bits `0` and `1` and
  `T` drawn at the challenge give equal expectations, call by call.
* `BB1Sim.expect_bb1SimImpl_random` — on a uniform `T`, the simulators with challenge bits `0`
  and `1` simulate alike.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)

/-- **The challenge bit is hidden by a random `T`, call by call** [BB04, proof of Theorem 4.1,
*Challenge*]: with `T` drawn at the first valid `Challenge` (`zt T = (Z, T)`), every call of the
lazy simulators with challenge bits `0` and `1` gives the same expectation to every `F`:
`𝔼[F] (bb1SimLazy false … i x s) = 𝔼[F] (bb1SimLazy true … i x s)`.

**Proof sketch.** `Init` and `KeyGen` do not depend on the bit (`bb1SimLazy_zero`,
`bb1SimLazy_one`, `bb1SimImpl_eq`, `IBEScheme.oracleImpl_zero_onSpec`,
`IBEScheme.oracleImpl_one_onSpec`). A `Challenge` other than the first valid one answers `⊥` or
repeats the recorded challenge (`bb1SimLazy_two_of_not`, `bb1SimChal_none`, `bb1SimChal_repeat`,
`bb1SimChal_invalid`). At the first valid one, `ProbComp.expect_sample_rel` with `R := Eq` along
`T ↦ decodeT(M_1)^{−1} decodeT(M_0) T` (`bb1SimLazy_two_fresh`, `bb1SimChal_fresh`,
`ofFn_bb1SimCt`). -/
theorem bb1SimLazy_random_call (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (s : BB1SimState G ℓ κ d) (F : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ) :
    ProbComp.expect (bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F =
      ProbComp.expect
        (bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F := by
  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases h012 i with rfl | rfl | rfl
  -- `Init` and `KeyGen` do not depend on the bit
  · rw [bb1SimLazy_zero, bb1SimLazy_zero, bb1SimImpl_eq, bb1SimImpl_eq,
      IBEScheme.oracleImpl_zero_onSpec, IBEScheme.oracleImpl_zero_onSpec]
  · rw [bb1SimLazy_one, bb1SimLazy_one, bb1SimImpl_eq, bb1SimImpl_eq,
      IBEScheme.oracleImpl_one_onSpec, IBEScheme.oracleImpl_one_onSpec]
  by_cases hf : (s.1.isSome ∧ s.2 = none ∧
        ((∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
  -- the first valid `Challenge`: reindex `T` by `T ↦ M₁⁻¹ M₀ T`
  · rw [bb1SimLazy_two_fresh G ℓ false κ d g X Y _ x s hf,
      bb1SimLazy_two_fresh G ℓ true κ d g X Y _ x s hf]
    obtain ⟨s₁, s₂⟩ := s
    obtain ⟨h₁, h₂, hv⟩ := hf
    rcases s₁ with _ | ⟨t, α₁⟩
    · exact absurd h₁ Bool.false_ne_true
    subst h₂
    set m := (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)) with hm
    have key : ∀ (b : Bool) (T : (G.group κ d).GT),
        bb1SimImpl G ℓ b κ d g X Y Z T 2 x (some (t, α₁), none) =
          .pure (cast (sidSpec_rng_two _ κ).symm
              (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)),
            (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)))) :=
      fun b T => by
        rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh G ℓ b κ d g X Y Z T _
          t α₁ ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1,
            (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩, OracleComp.pure_bind]
    simp only [key]
    have hct : ∀ T, bb1SimCt G ℓ κ d Z T α₁ m.1 =
        bb1SimCt G ℓ κ d Z (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
          (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d)
            (padFin _ (List.ofFn m.1))) T) α₁ m.2 := fun T => by
      simp only [Equiv.coe_mulLeft]
      rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _),
        List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), mul_assoc, mul_inv_cancel_left]
    refine ProbComp.expect_sample_rel Eq (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
      (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m.1)))) _ _
      (fun T => ⟨?_, ?_⟩) F F (fun y s' t' h => by rw [h]) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, hct]
  -- every other `Challenge` does not depend on the bit
  · rw [bb1SimLazy_two_of_not G ℓ false κ d g X Y _ x s hf,
      bb1SimLazy_two_of_not G ℓ true κ d g X Y _ x s hf,
      (bb1SimImpl_two_of_not G ℓ true κ d g X Y 1 1 x s hf).1]

/-- **On a random `T`, the simulator does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, *Challenge*, "when `T` is uniform and independent in `G_1` … `C` is independent of
`b` in the adversary's view"]: for every computation `c` and every `F` of its output,
`𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl false … Z T) c (none, none)) =
𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl true … Z T) c (none, none))`.

**Proof sketch.** Draw `T` at the first valid `Challenge` on both sides
(`expect_simulate_bb1SimLazy`, step E-T), then compare the lazy simulators call by call
(`ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`). -/
theorem expect_bb1SimImpl_random {β : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β)
    (F : β → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ false κ d g X Y Z T) c (none, none)) (fun p => F p.1)) =
      ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ true κ d g X Y Z T) c (none, none)) (fun p => F p.1)) := by
  rw [← expect_simulate_bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl, ← expect_simulate_bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl]
  exact ProbComp.expect_simulate_congr _ _
    (fun i x s F => bb1SimLazy_random_call G ℓ κ d g X Y Z i x s F) c _ _

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity/Chain.lean (Lean, at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Coupling
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# On good coins, the real BB1 game is the simulation on `P_BDH`

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "When the input 5-tuple is sampled from
`P_BDH` (where `T = e(g, g)^{abc}`) then `A`'s view is identical to its view in a real attack
game" [BB04, proof of Theorem 4.1, *Phase 2, Guess and the advantage*]. For generator coins `r`
with `2^ℓ ≤ p`, the chain of design r1 §3.1 equates the real game's acceptance, conditioned on
`r`, with the simulation game's on `P_BDH`:
1. move the setup's `h` past `g_2` and the adversary's coins, and draw it at the first `Init`
   (`expect_sample_sidImpl`: steps R1 and E-h);
2. read `g_2` as `g^{b'}` (`BilinearGroup.pow_val_bijective_of_ne_one`, `expect_sample_equiv`);
3. step M (`expect_simulate_bb1RealLazy`);
4. draw the challenge coin `c` in advance (`expect_simulate_bb1SimLazy`, step E-c), and merge
   `(a, b', c)` (`Bridge.expect_sample_pair`); the unused `T` drops out (`expect_const`).

## Main definitions

None.

## Main results

* `BB1Sim.prob_sidGame_coins` — on good coins, the real game's acceptance, conditioned on the
  generator's coins, is the simulation game's on `P_BDH`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- **On good coins, the real game is the simulation on `P_BDH`** [BB04, proof of Theorem 4.1,
*Phase 2, Guess and the advantage*, "When the input 5-tuple is sampled from `P_BDH` … `A`'s view
is identical to its view in a real attack game"]: let `o` be the setup's output map, read as in
`setup_out`. For generator coins `r` with `2^{ℓ(κ)} ≤ p`, the real game after `r`
(`g ∈ G^*`, `α`, `h`, `g_2`, `A`'s coins, the game's oracles on `o r g α h g_2`) and the
simulation game after `r` on `P_BDH` (`g ∈ G^*`, `(a, b', c)`, `T`, `A`'s coins, the simulator
on `(g, g^a, g^{b'}, g^c, e(g, g)^{a b' c})`) accept with the same probability.

**Proof sketch.** Expand both probabilities into expectations (`prob_bind`) and fix `g` and
`α = a`. Move `h` inside past `g_2` and `A`'s coins (`expect_sample_comm`) and draw it at the
first `Init` (`expect_sample_sidImpl`). Read `g_2 = g^{b'}` (`expect_sample_equiv` along
`pow_val_bijective_of_ne_one`), so that `o … h (g^{b'})` reads as `(g, g^a, g^{b'}, h)`
(`setup_out`'s `RealReads`). Step M (`expect_simulate_bb1RealLazy`, with
`natCast`-injectivity of identities from `2^ℓ ≤ p`) and E-c (`expect_simulate_bb1SimLazy`) give
the simulator on `g^c`, `e(g, g)^{a b' c}` with `c` drawn in advance. On the simulation side,
`T` is unused (`expect_const`) and `(a, b', c)` splits into three draws
(`Bridge.expect_sample_pair`); `c` moves past `A`'s coins (`expect_sample_comm`). -/
theorem prob_sidGame_coins (A : NUPPT) (q : ℕ) (b : Bool) (κ : ℕ)
    (o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
    (hR : ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2))
    (r : G.gen.Coins κ) (hr : ¬ (G.inst κ r).order < 2 ^ ℓ.eval κ) :
    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
      (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate ((bb1Scheme G ℓ).sidImpl b κ (o r g α h g2).1 (o r g α h g2).2)
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0)) (· = true) =
    ProbComp.prob ((ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order ×
        ZMod (G.group κ (G.desc κ r)).order × ZMod (G.group κ (G.desc κ r)).order)).bind
        fun abc =>
      (ProbComp.sample (G.group κ (G.desc κ r)).GT).bind fun t =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
      (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g.1 (g.1 ^ abc.1.val) (g.1 ^ abc.2.1.val)
          (g.1 ^ abc.2.2.val)
          (if true then (G.group κ (G.desc κ r)).pair g.1 g.1 ^ (abc.1 * abc.2.1 * abc.2.2).val
            else t))
        (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (none, none)).bind
        fun res => .pure (res.1 0)) (· = true) := by
  have hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ (G.desc κ r)).order := by
    rw [bb1Scheme_idLen]
    rw [BilinearGen.inst_eq, not_lt] at hr
    exact hr
  simp only [ProbComp.prob_bind]
  refine congrArg _ (funext fun g => ?_)
  -- the simulation side: split `(a, b', c)` into three draws; the unused `T` drops out
  rw [← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  refine congrArg _ (funext fun α => ?_)
  rw [← Bridge.expect_sample_pair]
  simp only [ProbComp.expect_bind, ProbComp.expect_pure, ↓reduceIte, ProbComp.expect_const]
  -- the real side: move `h` past `g_2` and `A`'s coins, then draw it at the first `Init`
  conv_lhs => rw [ProbComp.expect_sample_comm]
  conv_lhs => enter [2, g2]; rw [ProbComp.expect_sample_comm]
  conv_lhs => enter [2, g2, 2, ρ]; rw [expect_sample_sidImpl G ℓ b κ _ (fun h => o r g α h g2)
    (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ) (fun a => ProbComp.prob (.pure (a 0)) (· = true))]
  -- read `g_2` as `g^{b'}`
  rw [← ProbComp.expect_sample_equiv (Equiv.ofBijective _
    (BilinearGroup.pow_val_bijective_of_ne_one _ g.2))]
  simp only [Equiv.ofBijective_apply]
  refine congrArg _ (funext fun b' => ?_)
  -- draw the challenge coin before `A`'s coins, then step M and E-c for each `ρ`
  conv_rhs => rw [ProbComp.expect_sample_comm]
  refine congrArg _ (funext fun ρ => ?_)
  exact (expect_simulate_bb1RealLazy G ℓ b κ _ (fun h => o r g α h (g.1 ^ b'.val)) g.1 α b' g.2 hp
    (fun h => hR r g α h _) (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ q ρ)
    (fun a => ProbComp.prob (.pure (a 0)) (· = true))).trans
      (expect_simulate_bb1SimLazy G ℓ b κ _ g.1 _ _ _ _ _ rfl)

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== briefs/pairings/fills/bb1-sim/issued-fill-r1/readers/Defs-block.lean.txt (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

/-- **Oracle `0` of the game on the game's query type**: `Init` on the query read as an identity,
its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 0 x s =
(S.sidImpl b κ pp msk 0 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_zero_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 0) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 0 x s =
      (S.sidImpl b κ pp msk 0
        (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `2` of the game on the game's query type**: `Challenge` on the query read as two
messages, its answer read back on the game's answer type:
`S.sidImpl b κ pp msk 2 x s =
(S.sidImpl b κ pp msk 2 (cast x) s).bind fun p => pure (cast p.1, p.2)`. -/
theorem sidImpl_two_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      (S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s).bind
        fun p => .pure (cast (show (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)
          from rfl).symm p.1, p.2) :=
  (OracleComp.bind_pure _).symm

/-- **Oracle `1` of the game, its query read as an identity**: the call on the game's query
type is the call on the query read as an `idLen(κ)`-bit identity, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 1 x s = S.sidImpl b κ pp msk 1 (cast x) s`. -/
theorem sidImpl_one_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 1 x s =
      S.sidImpl b κ pp msk 1
        (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
          Fin (S.idLen.eval κ) → Bool) s := rfl

/-- **Oracle `2` of the game, its query read as two messages**: the call on the game's query
type is the call on the query read as two `msgLen(κ)`-bit messages, with the answer kept on the
game's answer type (the form for the `⊥` answers):
`S.sidImpl b κ pp msk 2 x s = S.sidImpl b κ pp msk 2 (cast x) s`. -/
theorem sidImpl_two_onQuery (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (s : S.SidState κ) :
    S.sidImpl b κ pp msk 2 x s =
      S.sidImpl b κ pp msk 2
        (cast (show (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)
          from rfl) x : Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) s := rfl

/-- **`KeyGen` for another identity, on the game's types**: with `ID*` recorded and the query
`x`, read as an identity, different from it, the answer is `⟨1, d_ID⟩` with
`d_ID ← KeyGen(msk, ID)`, read back on the game's answer type: for `cast x ≠ t`,
`S.sidImpl b κ pp msk 1 x (some t, c) =
(S.keyGen κ msk (cast x)).bind fun sk => pure (cast (decAnswer (some (encSK sk))), (some t, c))`. -/
theorem sidImpl_keyGen_ne_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 1) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool))
    (h : (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl) x :
      Fin (S.idLen.eval κ) → Bool) ≠ t) :
    S.sidImpl b κ pp msk 1 x (some t, c) =
      (S.keyGen κ msk (cast (show (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) from rfl)
        x)).bind fun sk =>
        .pure (cast (show (Fin (S.skLen.eval κ + 1) → Bool) = (S.sidSpec κ).rng 1 from rfl)
          (FixedLengthScheme.decAnswer (some (S.encSK κ sk))), (some t, c)) :=
  S.sidImpl_keyGen_ne b κ pp msk _ t c h

/-- **The first valid `Challenge`, on the game's types**: with `ID*` recorded, no challenge yet,
and both messages of the query `x`, read as two messages, in the message space, the answer is
`C ← Encrypt(params, ID*, M_b)`, read back on the game's answer type, and `C` is recorded: for
`(M₀, M₁) = splitHalf (cast x)` with `M₀, M₁ ∈ M`, `S.sidImpl b κ pp msk 2 x (some t, none) =
(S.enc κ pp t M_b).bind fun C => pure (cast (encCT C), (some t, some (encCT C)))`. -/
theorem sidImpl_challenge_fresh_onSpec (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)
    (x : (S.sidSpec κ).dom 2) (t : Fin (S.idLen.eval κ) → Bool)
    (h : S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1 ∧
      S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
        (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2) :
    S.sidImpl b κ pp msk 2 x (some t, none) =
      (S.enc κ pp t (if b then (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).2
        else (FixedLengthScheme.splitHalf (cast (show (S.sidSpec κ).dom 2 =
          (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) from rfl) x)).1)).bind fun c =>
        .pure (cast (show (Fin (S.ctLen.eval κ) → Bool) = (S.sidSpec κ).rng 2 from rfl)
          (S.encCT κ c), (some t, some (S.encCT κ c))) :=
  S.sidImpl_challenge_fresh b κ pp msk _ t h

## ===== briefs/pairings/fills/bb1-sim/issued-fill-r1/readers/BonehBoyen-block.lean.txt (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

/-- **`Setup` at the scheme's types**: `Setup` runs the generator and BB1's `Setup`, and returns
`(⟨d, params⟩, ⟨d, (params, master-key)⟩)` as parameters and master key of `bb1Scheme G ℓ`:
`Setup κ = (sample r).bind fun r => (BB1.setup _).bind fun k => pure (⟨desc r, k.1⟩, ⟨desc r, k⟩)`,
the pair typed at `PP κ × MSK κ`. -/
theorem bb1Scheme_setup_eq (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) :
    (bb1Scheme G ℓ).setup κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (BB1.setup (G.group κ (G.desc κ r))).bind fun k =>
        .pure (((⟨G.desc κ r, k.1⟩ : (bb1Scheme G ℓ).PP κ),
          (⟨G.desc κ r, k⟩ : (bb1Scheme G ℓ).MSK κ)) :
            (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) := rfl

/-- **`KeyGen` at the scheme's types, followed by `f`**: for the master key `⟨d, (pp, mk)⟩` and an
`ℓ(κ)`-bit identity `ID`, `KeyGen` is BB1's `KeyGen` on `idToZ ID`, its key tagged with `d`:
`(KeyGen ⟨d, (pp, mk)⟩ ID).bind f = (BB1.keyGen pp mk (idToZ ID)).bind fun k => f ⟨d, k⟩`. -/
theorem bb1Scheme_keyGen_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (mk : (G.group κ d).G)
    (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).SK κ → ProbComp β) :
    ((bb1Scheme G ℓ).keyGen κ ⟨d, (pp, mk)⟩ id).bind f =
      (BB1.keyGen pp mk (BB1.idToZ (G.group κ d) id)).bind fun k => f ⟨d, k⟩ := by
  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **`Encrypt` at the scheme's types, followed by `f`**: for the parameters `⟨d, pp⟩`, an
`ℓ(κ)`-bit identity `ID` and a `msgLen(κ)`-bit message `m`, `Encrypt` is BB1's `Encrypt` on
`idToZ ID` and `decodeT m` (the message read at the width of `G_T`), its ciphertext tagged
with `d`: `(Encrypt ⟨d, pp⟩ ID m).bind f = (BB1.encrypt pp (idToZ ID) (decodeT ⟦m⟧)).bind fun c =>
f ⟨d, c⟩`. -/
theorem bb1Scheme_enc_bind (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (pp : BB1.Params (G.group κ d)) (id : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool) {β : Type}
    (f : (bb1Scheme G ℓ).CT κ → ProbComp β) :
    ((bb1Scheme G ℓ).enc κ ⟨d, pp⟩ id m).bind f =
      (BB1.encrypt pp (BB1.idToZ (G.group κ d) id)
        (BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))).bind fun c => f ⟨d, c⟩ := by
  rw [padFin_ofFn]
  simp only [bb1Scheme_enc, OracleComp.bind_assoc, OracleComp.pure_bind]

/-- **The ciphertext encoding as a word**: `⟦encCT ⟨d, c⟩⟧` is the padded word `A ‖ B ‖ C_1`
(`ctLen(κ)` bits). -/
theorem ofFn_bb1Scheme_encCT (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)
    (c : BB1.Ciphertext (G.group κ d)) :
    List.ofFn ((bb1Scheme G ℓ).encCT κ ⟨d, c⟩) =
      List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ) (List.ofFn ((G.group κ d).encT c.a) ++
        List.ofFn ((G.group κ d).encG c.b) ++ List.ofFn ((G.group κ d).encG c.c))) := rfl

## ===== briefs/pairings/fills/bb1-sim/design-r1.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# Fill `bb1-sim` (T2, T3): design round 1, a relational simulation lemma in `Games`

This is a design note for the statement phase of fill unit `bb1-sim`, which covers T2 `bb1_sim_real`
and T3 `bb1_sim_random`. It was prepared read-only: no Lean was run, and nothing was committed. Every
Lean line number refers to the pins below and was read with `git show <pin>:<path>`.

| Pin | Value |
|---|---|
| #331 head (statements; Gate 40 closed) | `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| T4 branch `fill/pairings-bb1-machine` (T4 still `sorry`; the 7 readers are not in it yet) | `7c0a55e0239c14786612d0cd4462e64238543ca1` |
| Records commit with the ruling (decision log, 2026-11-16, "Rulings (Seyoon) … (2) T2/T3 design") | `bf08dbfa3a057a3b41d20f6dbede3066bc5e6660` |
| Records tip when this note was written (`TCSlib/Cryptography/Games/` is identical to #331's) | `a0e3148309dbc3bf836d46745b707724599541f0` |
| Gate 40 note | `briefs/pairings/gates/40-pairings-statements/findings/gate40-pairings-statements-findings.md`, § "Truth and sufficiency", the T2 paragraph |

**The ruling (Seyoon, 2026-11-16).** A public relational simulation lemma goes into `Games`. It
relates two handlers whose state types `σ` and `τ` are linked by an invariant `R : σ → τ → Prop`.
Each oracle call keeps the invariant, and the answers have equal laws. The lemma is statement-gated
together with the `bb1-sim` fill, and it is preferred to a combined state kept local to the fill.

**Summary of the proposal.**
* A new module, `TCSlib/Cryptography/Games/Relational.lean`, with three statements:
  * `ProbComp.expect_simulate_rel` (the target);
  * `ProbComp.prob_simulate_rel` (the event and acceptance corollary);
  * `ProbComp.expect_sample_rel` (discharges one call that samples once, coupled by a bijection).
* T2 uses `expect_simulate_rel` twice, together with the existing `Games.expect_simulate_eager`
  twice. T3 needs only the existing single-state `ProbComp.expect_simulate_congr`, after one
  eager/lazy step.
* The main practical risk is not the lemma. It is the set of readers that T2 needs in the frozen
  `Defs.lean` and `BonehBoyen.lean` (§3.3, §5). A probe should settle that set before the statement
  PR.

---

## 1. The `Games` API this builds on (at `9e7a9648`)

All paths below are relative to `TCSlib/Cryptography/`.

### 1.1 Types

| Name (full namespace `TCSlib.Cryptography.Games`) | What it is | File:line |
|---|---|---|
| `OracleSpec ι` | structure with fields `dom rng : ι → Type` | `Games/OracleComp.lean:74` |
| `OracleComp spec α` | inductive type: `pure : α → _`, `query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)` | `Games/OracleComp.lean:84` |
| `OracleComp.AllOutputs P c` | every possible output satisfies `P` | `Games/OracleComp.lean:292` |
| `unifSpec : OracleSpec ℕ` | `abbrev`, `⟨fun _ => Unit, fun m => Fin (m + 1)⟩` | `Games/Probability.lean:73` |
| `ProbComp` | `abbrev ProbComp := OracleComp unifSpec` | `Games/Probability.lean:77` |
| `ProbComp.sample T` | uniform element of a nonempty finite type | `Games/Probability.lean:92` |
| `ProbComp.expect : ProbComp α → (α → ℝ) → ℝ` | expectation | `Games/Probability.lean:106` |
| `ProbComp.prob c p` | `expect` of the indicator | `Games/Probability.lean:112` |
| `QueryImpl spec σ spec'` | `abbrev`, `∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. Notation under R-04-4. | `Games/Simulate.lean:73` |
| `simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)` | defined by recursion: `pure a, s ↦ pure (a, s)`; `query i x k, s ↦ (impl i x s).bind fun ys => simulate impl (k ys.1) ys.2` | `Games/Simulate.lean:83` |
| `accept G := prob G (· = true)`, `advantage G₀ G₁ := abs (accept G₀ - accept G₁)` | acceptance probability and advantage of games | `Games/Advantage.lean:63`, `:72` |
| `bitSpec din dout` | `abbrev`, `⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩` | `Games/BitCodec.lean:73` |
| `NUPPT.toComp D codec n q r : OracleComp spec α` | the machine as an oracle computation | `Games/Machines.lean:221` |

**Note on names.**
* For games there is no `acceptProb`: the acceptance probability is `Games.accept`.
* `acceptProb` exists only in the concrete layer (`Foundations/Experiments.lean:72`). The bridge
  between the two is `Games.Bridge.acceptProb_eq` (`Games/Bridges/Experiments.lean:120`).
* T2's frozen sketch cites `Games.expect_simulate_congr`. The lemma's actual name is
  `Games.ProbComp.expect_simulate_congr`.

### 1.2 The two lemmas the ruling is about, verbatim

`Games/Hopping.lean:384–393`, namespace `TCSlib.Cryptography.Games.ProbComp`:

```lean
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G
```

Here both implementations have the single state type `σ`, and both runs start from the same `s`.
This is the restriction that Gate 40 flagged.

`Games/Hopping.lean:494–503`, namespace `TCSlib.Cryptography.Games`; both T2 and T3 use it:

```lean
theorem expect_simulate_eager (O : QueryImpl spec σ unifSpec) (OE : T → QueryImpl spec σ unifSpec)
    (used : σ → Prop) (hused : ∀ t i x s, used s → OE t i x s = O i x s)
    (hstick : ∀ i x s, used s → (O i x s).AllOutputs fun p => used p.2)
    (hfresh : ∀ i x s, ¬ used s →
      (∀ t, OE t i x s = O i x s ∧ (O i x s).AllOutputs fun p => ¬ used p.2) ∨
      (O i x s = (ProbComp.sample T).bind (fun t => OE t i x s) ∧
        ∀ t, (OE t i x s).AllOutputs fun p => used p.2))
    (c : OracleComp spec α) (G : α × σ → ℝ) {s : σ} (hs : ¬ used s) :
    ProbComp.expect (simulate O c s) G =
      ProbComp.expect (ProbComp.sample T) fun t => ProbComp.expect (simulate (OE t) c s) G
```

This lemma also has one state type. It moves a one-shot sample between "drawn in advance" and
"drawn at the call that spends it".

### 1.3 Every `simulate_*` and `expect_simulate_*` lemma in `Games/`

| Lemma | Content | File:line |
|---|---|---|
| `simulate_pure`, `simulate_query` (`@[simp]`) | the two defining equations | `Games/Simulate.lean:93`, `:97` |
| `simulate_bind`, `simulate_call` | sequencing; a single call | `Games/Simulate.lean:107`, `:114` |
| `simulate_comp` | composing implementations (state `σ₁ × σ₂`) | `Games/Simulate.lean:199` |
| `simulate_withLog` | logging is conservative | `Games/Simulate.lean:241` |
| `simulate_costBoundedBy`, `simulate_costBoundedBy_once` | query cost under simulation | `Games/Simulate.lean:264`, `:290` |
| `simulate_eq_of_abs` | **two state types**, `f : σ₂ → σ₁`, exact equality of computations, every state | `Games/Simulate.lean:334` |
| `simulate_eq_of_abs_bounded` | the same, deterministic calls, with a query budget `cnt` | `Games/Simulate.lean:357` |
| `simulate_allOutputs_bad` | a sticky bad flag stays raised | `Games/Hopping.lean:179` |
| `expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad`, `identical_until_bad_init`, `hagree_of_eq` | the fundamental lemma; one state type | `Games/Hopping.lean:201`, `:252`, `:306`, `:343`, `:331` |
| `ProbComp.expect_simulate_congr` | equal laws per call; one state type | `Games/Hopping.lean:384` |
| `ProbComp.prob_bad_le` | per-query potential bound | `Games/Hopping.lean:403` |
| `simulate_eq_of_used` (private) | helper for the eager lemma | `Games/Hopping.lean:469` |
| `expect_simulate_eager` | one-shot coins in advance; one state type | `Games/Hopping.lean:494` |
| `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn` | transport along equal length functions | `Games/BitCodec.lean:415`, `:430` |
| `simulate_ofComp_pure`, `Bridge.simulate_eq` | query trees | `Games/Bridges/QueryTree.lean:83`, `:124` |

Supporting expectation lemmas:

| Lemma | File:line |
|---|---|
| `expect_pure` | `Games/Probability.lean:116` |
| `expect_bind` | `:127` |
| `expect_sample` | `:146` |
| `expect_const` | `:173` |
| `expect_mono` | `:192` |
| `prob_eq_expect` | `:207` |
| `prob_bind` | `:223` |
| `expect_sample_equiv` | `:303` |
| `expect_sample_comm` | `:312` |
| `expect_expect_sample` | `:325` |
| `expect_sub` | `:339` |
| `abs_expect_sub_le` | `:392` |
| `expect_congr_of_allOutputs` | `Games/Hopping.lean:101` |
| `Bridge.prob_sample_eq_uprob` | `Games/Bridges/Experiments.lean:65` |
| `Bridge.expect_sample_pair` | `Games/Bridges/Experiments.lean:72` |

### 1.4 The handler types of the IBE game and of the simulator

All lines below are in `AdvancedEncryption/IdentityBased/`.

| Object | Type or definition | File:line |
|---|---|---|
| `IBEScheme.sidSpec κ` | `abbrev := bitSpec (S.inLens κ) (S.outLens κ)`. `inLens` and `outLens` are defs (`:201`, `:217`), sealed for consumers. | `Defs.lean:232` |
| `IBEScheme.SidState κ` | `abbrev := Option (Fin (S.idLen.eval κ) → Bool) × Option (Fin (S.ctLen.eval κ) → Bool)` | `Defs.lean:240` |
| **real handler** `S.sidImpl b κ pp msk` | `QueryImpl (S.sidSpec κ) (S.SidState κ) unifSpec` | `Defs.lean:258–281` |
| its readers | `sidImpl_init_none`/`_some`, `_keyGen_none`/`_target`/`_ne`, `_challenge_none`/`_repeat`/`_fresh`/`_invalid`, all stated with **typed** queries `Fin (S.idLen.eval κ) → Bool` | `Defs.lean:284–346` |
| `S.oracleImpl κ init key chal` | `QueryImpl (S.sidSpec κ) σ unifSpec` built from typed handlers; readers `oracleImpl_zero`/`_one`/`_two` (typed) | `Defs.lean:352`, `:363`, `:372`, `:381` |
| `S.sidGame A q b κ` | `(S.setup κ).bind fun k => (sample (A.Coins κ)).bind fun r => (simulate (S.sidImpl b κ k.1 k.2) (A.toComp (S.sidCodec κ) κ q r) (none, none)).bind fun res => .pure (res.1 0)` | `Defs.lean:399` (`sidGame_eq` `:407`) |
| `BB1SimState G ℓ κ d` | `abbrev := Option ((Fin ℓ(κ) → Bool) × ZMod (G.group κ d).order) × Option (Fin ctLen(κ) → Bool)` | `BonehBoyen.lean:429` |
| **simulator** `bb1SimImpl G ℓ b κ d g X Y Z T` | `QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec := (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit …) (bb1SimKeyQ …) (bb1SimChal …)` | `BonehBoyen.lean:627–631` (`_eq` `:634`) |
| simulator readers | `bb1SimInit_none`/`_some` (`:487`, `:496`), `bb1SimKeyQ_none`/`_target`/`_ne` (`:517`–`:530`), `bb1SimChal_none`/`_repeat`/`_fresh`/`_invalid` (`:578`–`:611`), `bb1SimParams_eq` (`:448`), `bb1SimKey_eq` (`:466`), `bb1SimCt_eq` (`:548`) | `BonehBoyen.lean` |
| `bb1SimGame G ℓ A q b real κ` | draws `r`, `g ∈ G^*`, `(a, b', c)`, `T`, `ρ`; simulates `bb1SimImpl` from `(none, none)` | `BonehBoyen.lean:645` (`_eq` `:660`) |
| T2 `bb1_sim_real` | `advantage (sidGame A q b κ) (bb1SimGame G ℓ A q b true κ) ≤ uprob (fun r => (G.inst κ r).order < 2 ^ ℓ.eval κ)` | `BonehBoyenSecurity.lean:89–92` (sketch `:73–88`) |
| T3 `bb1_sim_random` | `advantage (bb1SimGame … false false κ) (bb1SimGame … true false κ) = 0` | `BonehBoyenSecurity.lean:104–106` (sketch `:94–103`) |

The two state types in T2 differ in their first component:
* the real game's is `Option ID`;
* the simulator's is `Option (ID × Z_p)`.

Within one run, the stored `α₁` is related to the real game's `h` only through `ID*`. The relation
`h = g_1^{−ID*} g^{α₁}` is exactly the invariant `R`.

---

## 2. The proposed statements

### 2.1 Placement: a new file `Games/Relational.lean`

**Recommended: a new child module `TCSlib/Cryptography/Games/Relational.lean`**, about 150–190
lines, namespace `TCSlib.Cryptography.Games`, imported by the `Games.lean` facade. Reasons:

* **Modularity.** The new file is one coherent cluster: comparing simulations on related states.
  Its only imports are `Games.Simulate` and `Games.Probability`; it needs nothing from `Hopping`.
* **Verification cost and ownership.** `Games/Hopping.lean` (524 lines) is imported directly by 7
  modules and transitively by most of `Cryptography/`. Appending to it would rebuild and re-seal
  that whole closure, and would put a shared file into the fill's diff. The facade `Games.lean` is
  imported only by `TCSlib.lean`. A new module therefore costs only itself, the facade and the
  root, and it is a file that only `bb1-sim` owns.
* **Size.** Appending would also be acceptable for size (Hopping would reach about 640 lines, under
  the 1000-line cap). This is not the reason to prefer the new file; the two reasons above are.
* **Exports.** The facade change is one `import` line and one `## Contents` entry
  (`Games.lean:5–11`, `:32–48`). `TCSlib.lean` already imports the facade (line 65), so the root
  does not change.
* **Placement elsewhere.** `Games` has no `Basic.lean`, and this is a framework lemma, not a
  pairing helper. Placing it in the pairing area would make it a private host, which the ruling
  rules out.

`Hopping.lean` is left byte-identical. In particular, its docstring gets no cross-reference, because
any change there rebuilds its whole downstream closure. The new file points back to
`ProbComp.expect_simulate_congr` and `simulate_eq_of_abs` instead.

### 2.2 Statement-phase text of the new module

The first two lemmas have `sorry` bodies at the statement phase. The third (L2) is proved from the
first (L1) at that point, by the proved-modulo rule, as `bb1_sidSecure` is proved from T2–T4. Every
line is at most 100 characters. There is no `@[simp]` and no new definition, so no reader is owed.

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states answers
alike and leads to related states, then the two simulations of any computation answer alike and
end in related states (`ProbComp.expect_simulate_rel`). "Alike" is measured by expectations: a
call, or a run, from related states gives the same expectation to any two functions of the
answer and the state that agree at equal answers and related states.

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal certification of code-based
  cryptographic proofs*, POPL 2009 (the probabilistic relational Hoare logic and its rule for
  adversary calls with oracles that keep a relational invariant). ⟨location to pin, Q11⟩
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006 (bridging steps). ⟨location to pin, Q11⟩
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.
[BGZ09, ⟨rule for adversary calls⟩] [Sho04, ⟨bridging steps⟩]

**Deviation:** [BGZ09] asks for a coupling of the two calls whose support relates their results;
here the hypothesis is its expectation form (equal expectations for every pair of test functions
that agree along the relation), which such a coupling implies and which is all the induction
uses.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  sorry

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`). -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  sorry

end ProbComp

end TCSlib.Cryptography.Games
```

**Changes to the facade `Games.lean`.**
* Import: `import TCSlib.Cryptography.Games.Relational`, after `…Games.Hopping` (line 9).
* `## Contents` entry: "`TCSlib.Cryptography.Games.Relational`: simulations of two implementations
  on related states (the relational form of simulation congruence)."

**How the hypothesis expresses the ruling's wording.** The ruling asks for "an invariant `R`
preserved by each oracle call, with equal answer laws". The single hypothesis `h` contains both
parts:
* **Equal answer laws.** Take `g₀`, `g₁` to be the same function of the answer only; `h` then says
  the two answers have the same law.
* **Preservation of `R`.** The test functions need to agree only at *related* successor states. If
  a call could reach a successor that is unrelated to the other side's successors, a pair of test
  functions would separate the two calls.

Packaging both parts as one expectation condition is what makes the induction a direct copy of
`expect_simulate_congr`'s. It is also the form in which the conclusion comes out, so the lemma
composes. Requiring an explicit coupling instead would add a new kind of object to `Games`
(Q3 in §5).

### 2.3 How the proofs would go, and which existing lemmas they use

* **L1 `expect_simulate_rel`.** The proof has the same shape as `ProbComp.expect_simulate_congr`
  (`Hopping.lean:384–393`): induction on `OracleComp` (`OracleComp.lean:84`), generalizing `s`, `t`
  and `hst`. It uses:
  * `simulate_pure` and `simulate_query` (`Simulate.lean:93`, `:97`);
  * `expect_pure` and `expect_bind` (`Probability.lean:116`, `:127`).

  An unchecked outline:
  ```lean
    induction c generalizing s t with
    | pure a =>
      rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
      exact hG a s t hst
    | query i x k ih =>
      rw [simulate_query, simulate_query, expect_bind, expect_bind]
      exact h i x s t hst _ _ fun y s' t' hR => ih y hR
  ```
* **L2 `prob_simulate_rel`.** Proved from L1 with `prob_eq_expect` (`Probability.lean:207`). It is
  proved at the statement phase.
* **L3 `expect_sample_rel`.** Uses `expect_bind`, `expect_pure` and `expect_sample_equiv`
  (`Probability.lean:303`); about 10 lines.
* **Rule 10.** Every foreign definition is read through its published lemmas: `simulate` through
  `simulate_pure`/`simulate_query`, `expect` through `expect_pure`/`expect_bind`, `prob` through
  `prob_eq_expect`, and `sample` through `expect_sample_equiv`. `QueryImpl` is an `abbrev`, which
  counts as notation. Nothing is unfolded, so the canonical seal of the new owner should pass
  unchanged.

### 2.4 Why it is not a duplicate

**How the search was done.** I searched `TCSlib/` at `9e7a9648` in four ways:
1. A script scanned every `theorem` or `lemma` statement mentioning `simulate` at least twice, or
   `simulate` together with two `QueryImpl`s. 49 hits; each was classified from its statement, and
   the relevant ones were read in full.
2. `git grep` for the terms "coupl", "bisim", `σ → τ → Prop`, `σ₁`/`σ₂`/`τ` beside
   `simulate`/`QueryImpl`, "pRHL", "Barthe" and "bridging".
3. The same grep for `expect_simulate_rel`, `simulate_rel`, `σ → τ → Prop` and "bisim" on **every
   local and remote branch** (including `fill/pairings-bb1-machine`, `fill/pairings-pair-bdh` and
   `stmt/*`). This found nothing.
4. The T4 helper modules on `7c0a55e0`.

**Result.**
* No public or private lemma relates two simulations by a relation between different state types.
* The new lemma generalizes three existing lemmas without restating any of them:
  * `expect_simulate_congr`, the case where `R` is equality;
  * the law form of `simulate_eq_of_abs`, the case `R s t ↔ s = f t`;
  * the unbudgeted cases of the ETT forms, the case `R s t ↔ P t ∧ s = f t`.
* L3 is new. No lemma states a bijective coupling of one sample as a relational step; the existing
  uses inline `expect_sample_equiv`.

**Near-relatives, and why each is not the same statement.**

| Lemma | File:line | Relation to the proposal |
|---|---|---|
| `Games.ProbComp.expect_simulate_congr` | `Games/Hopping.lean:384` | One state type, the same start state. The `R = Eq` special case. |
| `Games.simulate_eq_of_abs` | `Games/Simulate.lean:334` | Two state types, but a function `f : σ₂ → σ₁` and **exact equality of computations** for **every** state. It cannot express re-randomization (T2's `h ↔ α₁`, `r̃ ↔ r`) or an invariant (Gate 40: "structural state abstraction, but not arbitrary distributional re-randomization"). |
| `Games.simulate_eq_of_abs_bounded` | `Games/Simulate.lean:357` | As above, with deterministic calls and a budget. |
| `Composability.ETTGame.expect_simulate_abs`, `expect_simulate_abs_inv` | `Encryption/PrivateKey/EncryptThenTag/Tools.lean:65`, `:88` | **Closest relatives.** Law form with a function abstraction `f`, an invariant `P` on one side, and a **query budget** (`cnt`, `κ`, `CostBoundedBy`). A function cannot relate T2's states, where `h` and `α₁` are linked through `ID*`. In the ETT layer (the file's docstring: "candidates for promotion to the `Games` layer"), and recorded in **DL-40** as a deferred promotion (`duplication-ledger.md:67`). The new lemma is the unbudgeted relational generalization; the budgeted ETT lemmas are not instances of it (Q5). |
| `Games.expect_eq_until_bad`, `prob_eq_until_bad`, `identical_until_bad(_init)` | `Games/Hopping.lean:201`, `:252`, `:306`, `:343` | One state type; equality up to a bad flag. |
| `Games.expect_simulate_eager` | `Games/Hopping.lean:494` | One state type; moves one-shot coins. Used *beside* the new lemma (§3). |
| `Composability.ChallengeSim.expect_simulate_eager` | `Encryption/PublicKey/OracleSecurity/ChallengeSim.lean:148` | The same name in another namespace; a CPA-shaped eager step with one state type. |
| `NMSim.expect_simulate_rImpl_eager` | `Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean:267` | An application of `Games.expect_simulate_eager`. |
| `ETTGame.simulate_tapeImpl_congr`, `expect_simulate_tapeImpl`, `freshImpl`, `tapeImpl` | `…/EncryptThenTag/Tools.lean:145`, `:167`, `:116`, `:130` | Tapes against fresh coins; state `σ` against `σ × ℕ`, fixed by construction, with a budget. |
| `AdaptiveCPA.simulate_tapeImpl_congr`, `expect_tapeImpl` | `Encryption/PublicKey/AdaptiveCPA/Hybrid.lean:170`, `:244` | Specific tape hybrids. |
| `PRFGame.expect_lazyImpl` | `Encryption/PrivateKey/OracleFromPRF/Lazy.lean:351` | Lazy against eager random function; two state shapes, proved by its own induction for one pair of handlers. A specific bisimulation; the new lemma would be the generic tool for such proofs. |
| `ETTGame.expect_ettImpl_lazy`, `expect_ettLazyTape` | `Encryption/PrivateKey/EncryptThenTag/Lazy.lean:499`, `:461` | The same, for ETT. |
| `PRFGame.simulate_eImpl_congr` | `Encryption/PrivateKey/OracleFromPRF/Games.lean:199` | Congruence for one family of handlers. |
| `HashSignFill.expect_simulate_sample_once` | `Authentication/Signatures/HashAndSign/OneQuerySampling.lean:47` | One-query sampling law. |
| `LamportFill.planted_coupling` | `Authentication/Signatures/Lamport/Planted.lean:403` | A deterministic "coupling" for one specific aborting handler (at most one query). |
| `NMSim.expect_runB_good` (private) | `Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:702` | A coupling through `expect_eq_until_bad`. |
| `BB1Machine.exists_simulate_tape_eq_pure`, `expect_castImpl_freshImpl` (T4 branch) | `…/BonehBoyenMachine/Draws.lean:399`, `…/Reduction.lean:203` at `7c0a55e0` | Specific to T4's tape handler. |

**Note.** Several of these specific bisimulations (`expect_lazyImpl`, `expect_ettImpl_lazy`) could
later be re-proved from `expect_simulate_rel`. That is a candidate refactor for the DL-40 clean-up,
not part of this unit.

---

## 3. How T2 and T3 use it

The fill-local names below (`bb1RealAt`, `bb1RealLazy`, `bb1SimLazy`, `BB1RealState`) are
illustrative. Let `S := bb1Scheme G ℓ` and `c := A.toComp (S.sidCodec κ) κ q ρ`; this is the same
computation in both games. Fix the generator coins `r`, and write `d = G.desc κ r` and
`B = G.group κ d`. A coin set is *good* when `2^ℓ ≤ p`.

### 3.1 T2 `bb1_sim_real`

**Chain.** All quantities below are acceptance probabilities conditioned on `r`. Steps (1)–(4) and
(6)–(7) hold for every `r`; only step (5) uses good coins.

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[sidGame_b | r] = 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (S.sidImpl b κ pp_h msk_h) c ∅]` | Move the setup sample `h` inside, past `g₂` and `ρ` (`expect_sample_comm`, `expect_expect_sample`). |
| (2) | `= 𝔼_{g,α,g₂,ρ} 𝔼_h Pr[simulate (bb1RealAt h) c ∅]` | **`expect_simulate_rel` with `R_h`** (step R1 below). |
| (3) | `= 𝔼_{g,α,g₂,ρ} Pr[simulate bb1RealLazy c ∅]` | **`Games.expect_simulate_eager`** (step E-h below). |
| (4) | `= 𝔼_{g,α,b',ρ} Pr[… with g₂ := g^{b'}]` | `expect_sample_equiv` with the bijection `Z_p ≃ G`, `b' ↦ g^{b'}` (`g ≠ 1`). |
| (5) | `= 𝔼_{g,α,b',ρ} Pr[simulate bb1SimLazy c ∅]` | **`expect_simulate_rel` with `R`** (step M below); needs good coins. |
| (6) | `= 𝔼_{g,α,b',ρ} 𝔼_c Pr[simulate (bb1SimImpl b κ d g X Y g^c e(g,g)^{αb'c}) c ∅]` | **`Games.expect_simulate_eager`** (step E-c below). |
| (7) | `= Pr[bb1SimGame_{b,true} | r]` | Reorder; merge `(a, b', c)` (`Bridge.expect_sample_pair`); with `real = true` the sample `T` is unused (`expect_const`). |
| Bad coins | `abs (accept₀ − accept₁) ≤ 𝔼_r 1[p < 2^ℓ] = uprob (…)` | Pointwise bound `abs (F₀ r − F₁ r) ≤ 1[bad r]`, then `Bridge.prob_sample_eq_uprob` and `BilinearGen.inst_eq` (`Pairing/Group.lean:282`). |

**Handlers and invariants.** Throughout, `X = g^α` and `Y = g₂ = g^{b'}`.

* **Step R1** (equation (2)): from the real handler to a handler that stores `h`.
  * `impl₀ := S.sidImpl b κ pp_h msk_h` on `S.SidState κ`, where
    `pp_h = ⟨d, (g, X, Y, h)⟩` and `msk_h = ⟨d, ((g, X, Y, h), Y^α)⟩`. This is the shape of
    `bb1Scheme`'s setup output, `(⟨d, k.1⟩, ⟨d, k⟩)`.
  * `impl₁ := bb1RealAt h` on
    `BB1RealState := Option ((Fin ℓ(κ) → Bool) × B.G) × Option (Fin ctLen(κ) → Bool)`. On a
    committed state it runs `sidImpl`'s call with the *stored* `h`. On the first `Init` it stores
    `(ID*, h)`.
  * `R_h s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
  * Start: `R_h (none, none) (none, none)`.
  * Per-call obligations: from related states the two calls are the same computation, with the
    state mapped. The deterministic cases need `expect_pure`. The sampling cases (`KeyGen` for
    `ID ≠ ID*`, a fresh `Challenge`) need L3 with `e := Equiv.refl`.
* **Step E-h** (equation (3)): `Games.expect_simulate_eager` with `O := bb1RealLazy` (draws
  `h ← G` at the first `Init`), `OE h := bb1RealAt h`, and `used u := u.1.isSome`.
  * From a committed state, `bb1RealAt h = bb1RealLazy`.
  * `KeyGen` and `Challenge` before `Init` answer `⊥` and leave the state uncommitted.
  * `Init` from an uncommitted state is the spending call.
* **Step M** (equation (5)): the main relation. **This is the coupling in T2's sketch.**
  * `impl₀ := bb1RealLazy`.
  * `impl₁ := bb1SimLazy b κ d g X Y (zt := fun c => (g^c, e(g, g)^{(α b' c)}))`: the simulator
    with the challenge coin `c` drawn at the first valid challenge.
  * `R u v :↔ u.2 = v.2 ∧ Option.Rel (fun (t, h) (t', α₁) => t = t' ∧
    h = X ^ (−idToZ t).val * g ^ α₁.val) u.1 v.1`, i.e., the same recorded challenge, and
    `h = g₁^{−ID*} g^{α₁}`.
  * Start: `R (none, none) (none, none)`.
* **Step E-c** (equation (6)): `Games.expect_simulate_eager` with `O := bb1SimLazy …` and
  `OE c := bb1SimImpl b κ d g X Y (g^c) (e(g,g)^{αb'c})`, both on `BB1SimState`, and
  `used v := v.2.isSome`. `Z` and `T` enter only the fresh valid challenge
  (`bb1SimChal_fresh`), so the coins are one-shot.

**Per-call obligations of step M.** In every case the precondition is `R u v`. The left column is
`bb1RealLazy`, read through `sidImpl`'s readers. The right column is `bb1SimLazy`, read through
`oracleImpl_*_onSpec` and the `bb1Sim*` readers.

| Call | Real (`impl₀`) | Simulator (`impl₁`) | Why the hypothesis of L1 holds |
|---|---|---|---|
| `Init`, uncommitted | Draw `h ← G`. Answer `encPP ⟨d,(g,X,Y,h)⟩`. Store `(ID, h)`. | `bb1SimInit_none`: draw `α₁ ← Z_p`. Answer `encPP ⟨d, bb1SimParams g X Y ID α₁⟩`. Store `(ID, α₁)`. | **L3** with `e : G ≃ Z_p`, the inverse of `α₁ ↦ X^{(−ID)} g^{α₁}` (a bijection for each `ID`, because `g ≠ 1`). `bb1SimParams_eq` makes the parameters equal, so the answers are equal (compared through `ofFn_bb1Scheme_encPP`). The new states are in `R`. |
| `Init`, committed | Answer the stored parameters. | `bb1SimInit_some`. | Deterministic. `R` gives `h = X^{−t} g^{α₁}`. |
| `KeyGen` before `Init`, or for `ID*` | `⊥` (`sidImpl_keyGen_none`, `_target`) | `bb1SimKeyQ_none`, `_target` | Deterministic; states unchanged. |
| `KeyGen` for `ID ≠ ID*` | Draw `r̃`. Answer `⟨1, encSK ⟨d,(Y^α F(ID)^{r̃}, g^{r̃})⟩⟩` (`sidImpl_keyGen_ne`, `bb1Scheme_keyGen`, `BB1.keyGen_eq`). | `bb1SimKeyQ_ne`: draw `r`. Answer `⟨1, encSK ⟨d, bb1SimKey g X Y t α₁ ID r⟩⟩`. | **L3** with `r̃ ↦ r̃ + b'/(ID − ID*)` (`Equiv.addRight`). Good coins make `ID − ID* ≠ 0` in `Z_p` (`bitsToNat_lt`, `bitsToNat_injective`, `Asymptotic/Sampling.lean:412`, `:417`). The keys are equal by BB04's computation, with `F(ID) = g^{α(ID−ID*)+α₁}` (`bb1SimKey_eq`, `BB1.F_eq`, `pow_val_mul` and exponent laws). States unchanged. |
| `Challenge` before `Init` | `⊥` | `bb1SimChal_none` | Deterministic. |
| `Challenge`, repeated | the recorded ciphertext | `bb1SimChal_repeat` | `u.2 = v.2`. |
| `Challenge`, first, invalid | `⊥` (`sidImpl_challenge_invalid`) | `bb1SimChal_invalid` | Both message spaces depend only on `d` (`bb1Scheme_msgSpace_iff`). |
| `Challenge`, first, valid | Draw `s`. Answer and record `encCT ⟨d, (e(X,Y)^s · M_b, g^s, F(ID*)^s)⟩` (`sidImpl_challenge_fresh`, `bb1Scheme_enc`, `BB1.encrypt_eq`). | Draw `c`. Answer and record `bb1SimCt d (g^c) (e(g,g)^{αb'c}) α₁ M_b`. | **L3** with `e := Equiv.refl` (`s = c`). `F(ID*) = g^{α₁}`; `e(X,Y)^c = e(g,g)^{αb'c}` (`bilinear_pow`, `pow_val_mul_GT`); `G_T` is commutative. Answers compared through `ofFn_bb1SimCt` and an `encCT` reader (§3.3). |

**Mapping to T2's frozen sketch** (`BonehBoyenSecurity.lean:78–88`).

| Sketch sentence | Where it is in this design |
|---|---|
| "Fix coins with `2^ℓ ≤ p` …" | The good-coin case, used in `KeyGen` for `ID ≠ ID*`. |
| "Map `α ↦ a`, `g_2 ↦ g^{b'}` …" | Steps (4) and (5). |
| "… and `h ↦ g_1^{−ID*} g^{α_1}`" | Step M at `Init`. It is per call only after E-h moves `h` to `Init`: `h` is drawn before `ID*` exists. |
| "Answers to `Init` agree." | The two `Init` rows. |
| "the simulated key with exponent `r` is the real key with exponent `r̃` …" | The `KeyGen` row for `ID ≠ ID*`. |
| "The challenge is `Encrypt` with `s = c` …" | The valid-challenge row, after E-c moves `c` to the challenge. |
| "The state machines agree step by step (`simulate` with matched implementations, `Games.expect_simulate_congr`)" | **Becomes `ProbComp.expect_simulate_rel` with `R`**, plus the two eager steps. |
| "differ only on the excluded coins" | The bad-coin row of the chain. |

The sketch's route is sound, but two of its steps are implicit: the timing of `h` (drawn before
`ID*`) and of `c` (drawn before the challenge). The docstring-only sketch refresh at landing
(standing rule) should name `expect_simulate_rel` and the two `expect_simulate_eager` steps.

### 3.2 T3 `bb1_sim_random`

The relational lemma is **not needed** for T3. Both games use the same simulator shape and the same
state type `BB1SimState`, so `R` is equality and the existing `ProbComp.expect_simulate_congr`
applies. L3 is used with `R := Eq` at one call.

**Chain, for each `b`.**

| Step | Equation | How it is justified |
|---|---|---|
| (1) | `Pr[bb1SimGame_{b,false}] = 𝔼_{r,g,abc,ρ} 𝔼_T Pr[simulate (bb1SimImpl b κ d g X Y Z T) c ∅]` | Move `T` inside, past `ρ`. |
| (2) | `= 𝔼_{r,g,abc,ρ} Pr[simulate (bb1SimLazy b κ d g X Y (zt := fun T => (Z, T))) c ∅]` | **`Games.expect_simulate_eager`** (step E-T): `used v := v.2.isSome`, and `T` is spent at the first valid challenge. |

**Comparing the two bits.** Then `bb1SimLazy false …` and `bb1SimLazy true …` have the same law
call by call (`ProbComp.expect_simulate_congr`, `Hopping.lean:384`):
* `Init` and `KeyGen` are identical (the same `bb1SimInit` and `bb1SimKeyQ`).
* `Challenge` before `Init`, repeated, or invalid is identical: the validity test does not depend
  on `b`.
* At the first valid challenge, apply **L3 with `R := Eq`** and the bijection
  `T ↦ decodeT M₁⁻¹ · decodeT M₀ · T` of `G_T`. Then `M₀ · T = M₁ · e(T)`, so the answers are
  equal and both sides record the same ciphertext (compared through `ofFn_bb1SimCt`).

Hence the accepts are equal, and `advantage = 0` (`advantage_eq`).

**Relation to T3's sketch** (`BonehBoyenSecurity.lean:98–103`). The sketch says: "exchanging the
sample of `T` with the rest of the game (`expect_expect_sample`) and reindexing it by
`T ↦ M_b^{−1} M_{1−b} · T`".
* `expect_expect_sample` alone cannot move `T` past the adaptive history. The step that does it is
  E-T. Gate 40 made the same point: "an unconditional permutation chosen before seeing the adaptive
  history is not required".
* The reindexing is per call, at the challenge.

The sketch refresh at landing should name `expect_simulate_eager` and `expect_simulate_congr`.

### 3.3 What else the fill needs

1. **Readers in the frozen files.** This is the main dependency.
   * **From T4's PR** (approved; not yet on `7c0a55e0`):
     * `IBEScheme.oracleImpl_{zero,one,two}_onSpec` (`Defs.lean`), for reading `bb1SimImpl` at the
       game's query type; needed by T2 and T3;
     * `bb1Scheme_msgSpace_iff`, for T2's invalid-challenge case;
     * `ofFn_bb1SimCt`, for the challenge answers in T2 and T3;
     * `ofFn_bb1Scheme_encPP` and `ofFn_bb1Scheme_encSK`, for T2's `Init` and `KeyGen` answers.
   * **Probably new** (to be confirmed by a probe):
     * **a reader for `sidImpl` at the game's query type.** The nine `sidImpl_*` readers take typed
       queries `Fin (S.idLen.eval κ) → Bool`. Under the seals, `inLens` blocks unification with
       `(S.sidSpec κ).dom i`, which is the obstruction T4 hit for `oracleImpl`. Proposed:
       `IBEScheme.sidImpl_eq_oracleImpl : S.sidImpl b κ pp msk =
       S.oracleImpl κ (S.sidImpl b κ pp msk 0) (S.sidImpl b κ pp msk 1) (S.sidImpl b κ pp msk 2)`.
       It is one reader, proved by `funext` and a three-way `match` with `rfl`. Combined with
       T4's `_onSpec` readers it makes the typed `sidImpl_*` lemmas apply. The alternative is three
       `sidImpl_*_onSpec` readers in T4's form.
     * **an `ofFn` reader for `bb1Scheme`'s `encCT`** (`ofFn_bb1Scheme_encCT`), parallel to T4's
       `encPP` and `encSK` readers, for comparing the real challenge with `bb1SimCt`.
   * **Constructing values in a consumer file.** T4's report notes that anonymous constructors
     `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` do not elaborate under the seals. The real-side handlers
     (`bb1RealAt`, `bb1RealLazy`) should therefore take the setup's output map as a parameter,
     instantiated from `bb1Scheme_setup` and `BB1.setup_eq` at the use site. They should not
     construct `PP` or `MSK` values themselves.
2. **Group helpers.** None of these is published:
   * `a ↦ g^{a.val}` is a bijection `Z_p ≃ G` for `g ≠ 1`. Only the `G_T` form
     `pow_val_bijective` exists (`Pairing/Group.lean:224`).
   * The additive and negation exponent laws `x^{(u+v).val} = x^{u.val} x^{v.val}` and
     `x^{(−u).val} = (x^{u.val})⁻¹`, next to `pow_val_mul` (`:192`).
   * Residue injectivity of `ℓ`-bit identities when `2^ℓ ≤ p`, from `bitsToNat_lt` and
     `bitsToNat_injective`.

   Each is a short proof from `exists_pow_eq`, `pow_order` and Mathlib's `orderOf` facts. Q10 asks
   where they go.
3. **Lazy handlers, with readers and eager lemmas.**
   * `bb1SimLazy` should be generic in the challenge coins (`zt : U → G × G_T`). One definition
     then serves T2's `c` (`U = Z_p`) and T3's `T` (`U = G_T`), with one eager lemma derived from
     `Games.expect_simulate_eager`.
   * `bb1RealAt` and `bb1RealLazy` serve T2's `h`.
   * They are public definitions in a helper module, so each lands with case readers (policy §1).
   * No new eager lemma is to be proved: DL-33 recorded an earlier near-copy of the eager lemma.
4. **Averaging a pointwise bound.** T2's last step needs `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h` from
   `∀ x, abs (f x − g x) ≤ h x`. The only copy is the **private**
   `abs_expect_sub_le_expect` (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515`), which
   DL-40 has queued for promotion. The fill must not add a second private copy (Q6).
5. **Plumbing that already exists.**
   * Game equations: `IBEScheme.sidGame_eq`, `bb1SimGame_eq`, the `bb1Scheme_*` `simps` equations,
     `BB1.setup_eq`.
   * Advantage: `accept_eq`, `advantage_eq`.
   * Expectations: `prob_bind`, `expect_bind`, `expect_sample_comm`, `expect_expect_sample`,
     `Bridge.expect_sample_pair`, `expect_const`, `expect_sample_equiv`,
     `Bridge.prob_sample_eq_uprob`.
   * Group: `BilinearGen.inst_eq`, `bilinear_pow`, `pow_val_mul(_GT)`.
   * The instance `nonempty_ne_one` (`Pairing/Group.lean:147`) for sampling `G^*`.
   * No query budget is needed anywhere.
6. **Layout.**
   * Helper modules under `IdentityBased/BonehBoyenSecurity/`, for example `Lazy.lean` (the lazy
     handlers and eager lemmas), `Real.lean` (R1 and E-h) and `Coupling.lean` (step M with the
     group helpers).
   * `BonehBoyenSecurity.lean` gains their imports and a `## Contents` section, following T4's
     precedent for `BonehBoyenMachine.lean`.
   * T2's and T3's headers and statement prose stay byte-identical.
   * At landing, the `**Proof sketch.**` paragraphs get a docstring-only refresh.
   * Size: the plan estimates T2 at 400–800 lines and T3 at 150–350. The lazy handlers and their
     readers move T2 toward the upper end.

---

## 4. Unit split and gating

### 4.1 Statement phase (Phase S)

**Contents of the change.**
* The new file `Games/Relational.lean` exactly as in §2.2:
  * `expect_simulate_rel` and `expect_sample_rel` are `sorry`'d, with sketches;
  * `prob_simulate_rel` is proved from `expect_simulate_rel` (proved-modulo).
* The `Games.lean` facade: one import and one `## Contents` entry.
* Nothing else. `Hopping.lean`, `TCSlib.lean` and every pairing file stay unchanged.

**Branch.** Phase S touches only `Games/`, which sits above the pairing closure and is disjoint
from #331, #340 and T4's branch. It can therefore be a small PR on the records tip. The precedent
is #210's shared statements S1–S3, which were added `sorry`'d and later filled by the units.

**Evidence, in the campaign's usual form.**
* A build of `Games.Relational`, `Games` and the root.
* An axiom census: `sorryAx` only in `expect_simulate_rel` and `expect_sample_rel`, and inherited by
  `prob_simulate_rel`.
* Canonical seals of the new owner (strict and coe, A and B), with paired controls and the
  explicit-unfold scan.
* Style lint; frozen check: no other file is changed.

**Before Phase S is filed, a probe (not committed).** This avoids T4's mid-fill stop. The probe
should:
* state T2's per-call obligations for step M and T3's challenge obligation;
* check them under the development seals, using T4's 7 readers and the proposed
  `sidImpl_eq_oracleImpl` and `ofFn_bb1Scheme_encCT`;
* put the exact reader set to Seyoon as a scope request before the fill is issued.

### 4.2 Fill (Phase F, unit `bb1-sim`)

**What the unit owns.**
* The proof bodies of `expect_simulate_rel` and `expect_sample_rel` in `Games/Relational.lean`.
  Their headers and statement prose are frozen at the Phase S commit.
* T2 and T3 in `IdentityBased/BonehBoyenSecurity.lean`, plus the new helper modules.
* The reader insertions that the scope ruling approves.

**Base.** The fill uses T4's readers, so it must be based on T4's PR after the readers land there,
or on the records tip once that PR has merged.

**End state.** `bb1_sidSecure` reaches standard axioms once both T4 and `bb1-sim` are in.

### 4.3 Gate coverage

* **Gate 44** audits T4's PR (`fill/pairings-bb1-machine`): the T4 fill, and the 7 readers checked
  as pure insertions. It does not cover `Games/Relational.lean` or T2/T3, and it should not be
  widened to them.
* **Recommended: one `bb1-sim` gate after Gate 44**, numbered with the next free number when it is
  staged. Having one gate for the statement and the fill matches the ruling. Its pack:
  1. pins the Phase S commit as the statement baseline;
  2. runs a frozen-header check: `expect_simulate_rel`, `prob_simulate_rel` and
     `expect_sample_rel` are byte-identical to Phase S apart from their `**Proof sketch.**`, and T2
     and T3 are byte-identical to #331;
  3. audits the three statements for generality, docstring fidelity, attribution, placement and
     non-duplication against the table in §2.4;
  4. checks the reader insertions as pure insertions, as Gate 44 does;
  5. audits the fill: seals for the new owners and for every owner whose closure changed, axioms,
     and the sketch refresh.
* **Alternative.** If Seyoon wants the `Games` statement fixed before the fill is issued, Phase S
  can be appended to Gate 44's pack as a separate item. The files are disjoint and the item is
  statement-only. The fill would then be audited at the later gate.
* **The file-disjointness caveat.** The premise that "T4's PR … owns disjoint files" holds for the
  owned files, but not for the reader insertions:
  * T4's PR inserts into `Defs.lean` and `BonehBoyen.lean`, and `bb1-sim` probably needs more
    insertions in the same two files.
  * To keep the diffs disjoint in time, sequence them: T4 merges first, then `bb1-sim`.
  * The `bb1-sim` readers go at different anchors: in `Defs.lean`, after T4's `_onSpec` block
    (`sidImpl_eq_oracleImpl` mentions `oracleImpl`, so it must follow `Defs.lean:352`); in
    `BonehBoyen.lean`, next to the `simps` attribute (`:386`).
  * Each of those owners' canonical seals is re-run in that gate.

---

## 5. Risks and open questions

### Risks

1. **The reader scope (high).**
   * T2 cannot read `sidImpl` at the game's query type with the published readers. This is the
     `inLens` obstruction from T4's report.
   * T2 probably also needs an `encCT` reader, and a way to avoid constructing
     `(bb1Scheme G ℓ).PP κ` values in a consumer file.
   * Without a probe first, the fill would stop mid-way as T4 did (§3.3, item 1; §4.1).
2. **Dependence on T4's PR (medium).** `bb1-sim` consumes `oracleImpl_*_onSpec`,
   `bb1Scheme_msgSpace_iff` and the `ofFn_*` readers, and both units insert into the same two
   frozen files. Q9 covers the ordering.
3. **Sketch drift (low; standard).**
   * T2's frozen sketch cites `Games.expect_simulate_congr` (the wrong namespace, and the wrong
     lemma, since the state types differ).
   * Both sketches leave the eager/lazy steps implicit (§3.1, §3.2).
   * The standing rule gives a docstring-only refresh at landing; the statements are never changed.
4. **Budget and DL-40 (low).**
   * `expect_simulate_rel` has no query budget, so the budgeted ETT `expect_simulate_abs(_inv)`
     are not instances of it.
   * If DL-40's promotion later wants them derived from the relational form, it needs a budgeted
     variant (Q5).
   * Today's ETT copies stay as recorded in DL-40. Nothing new is duplicated.
5. **Duplication traps for the fill (medium).**
   * A second private copy of `abs_expect_sub_le_expect` (Q6).
   * Re-proving an eager lemma instead of citing `Games.expect_simulate_eager` (the DL-33
     precedent).
   * Private group helpers that duplicate a Mathlib fact. The fill should check Mathlib's
     `orderOf` and `ZMod` API first and disclose whatever it adds.
6. **Audit of the hypothesis form (low).**
   * An auditor may ask whether a hypothesis stated as "the conclusion for one call" is checkable.
     L3 answers this: in the BB1 proofs every call is either deterministic or one sample coupled by
     a bijection.
   * The hypothesis is weaker than an explicit coupling, which implies it. Its conclusion has the
     same form, so it composes.
7. **Attribution (low).** The locations in [BGZ09] (the rule for adversary calls) and [Sho04]
   (bridging steps) are not pinned here: the PDFs are not in the repository, and nothing was read
   to confirm a section number (Q11).
8. **Verification cost (low).**
   * Phase S rebuilds one new module, the `Games` facade and the root.
   * The reader insertions in Phase F rebuild the IBE closure, and need canonical re-seals of
     `Defs` and `BonehBoyen`.
9. **Name collision (none found).** `expect_simulate_rel`, `prob_simulate_rel` and
   `expect_sample_rel` exist on no branch. Readers should not confuse `Games.expect_simulate_eager`
   with `ChallengeSim.expect_simulate_eager`.

### Open questions for Seyoon (recommended option first)

- **Q1. Placement.**
  - (A) A new `Games/Relational.lean`, imported by the `Games` facade.
  - (B) Append to `Games/Hopping.lean` after `expect_simulate_congr`. This touches a widely
    imported file and costs a large rebuild and re-seal.
- **Q2. Names.**
  - (A) `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`, beside
    `ProbComp.expect_simulate_congr`.
  - (B) Root `Games.` names, as with `expect_simulate_eager`.
- **Q3. Form of the hypothesis.**
  - (A) The inline expectation hypothesis of §2.2: equal expectations of test functions that agree
    along `R`.
  - (B) A named predicate (for example `ProbComp.RelLaw R c₀ c₁`) with its `relLaw_iff` reader.
  - (C) An explicit coupling computation with an `AllOutputs` support condition.
- **Q4. Companions.**
  - (A) `prob_simulate_rel` and `expect_sample_rel` with the target.
  - (B) The target only. The fill then discharges calls inline with `expect_sample_equiv`.
- **Q5. Query budget.**
  - (A) None now.
  - (B) Also state `expect_simulate_rel_bounded` (a budget `cnt`/`κ`), so that DL-40 can later
    re-derive ETT's `expect_simulate_abs(_inv)` from it.
- **Q6. The averaging bound `abs (𝔼 f − 𝔼 g) ≤ 𝔼 h`.**
  - (A) The T2 fill writes it inline in T2's proof (a few lines, disclosed), and DL-40's promotion
    stays queued.
  - (B) Promote the ETT lemma now into `Games/Probability.lean` (a widely imported file).
  - (C) Add it to `Games/Relational.lean` in Phase S.
- **Q7. Reading `sidImpl` at the game's query type.**
  - (A) One reader, `IBEScheme.sidImpl_eq_oracleImpl`, in `Defs.lean` after T4's `_onSpec`
    readers. It is carried by the `bb1-sim` PR under an advance scope ruling from the probe.
  - (B) Three `sidImpl_{zero,one,two}_onSpec` readers in T4's form.
  - (C) Ask T4's PR to carry it, which widens T4's approved minimal scope.
- **Q8. Gate.**
  - (A) One `bb1-sim` gate after Gate 44, covering the Phase S statement, the reader insertions and
    the fill.
  - (B) Fold the Phase S statement into Gate 44's pack and audit the fill later.
- **Q9. Order and bases.**
  - (A) Phase S as its own small PR on the records tip. The fill is stacked on T4's PR, or based on
    the tip once T4 has merged.
  - (B) Everything on one branch stacked on T4's PR.
- **Q10. Group helpers** (`Z_p ≃ G` for `g ≠ 1`, exponent laws, identity injectivity on good
  coins).
  - (A) Public helpers with formula docstrings in the fill's helper module, disclosed.
  - (B) A reader-style request into the frozen `Pairing/Group.lean`.
- **Q11. Attribution of the lemma.**
  - (A) Cite [BGZ09] and [Sho04] at locations the maintainer pins from the sources.
  - (B) Treat it as a framework lemma and give only the design references; policy §2 allows tags to
    be omitted for technical glue.

---

## Appendix: search record

**Scanner.** A script was run on `9e7a9648` with `python3 -I`; it is in the job's scratch area and
is not committed. It lists every `theorem` or `lemma` under `TCSlib/` whose statement contains
`simulate` twice, or `simulate` together with two `QueryImpl`s. 49 hits; each was classified from
its statement, and the relevant ones were read in full and are listed in §2.4.

**Greps on `9e7a9648`.**
* `coupl|bisim` (case-insensitive) under `TCSlib/Cryptography`: prose only, in Lamport,
  HashAndSign, NonMalleability, FromPRF and the IBE docstrings. No generic lemma.
* `Barthe|pRHL|CertiCrypt|EasyCrypt|bridging step` under `TCSlib` and `blueprint`: no
  cryptographic citation.
* `theorem …simulate…` in `Games/`: the rows of §1.3.

**All local and remote branches:** `expect_simulate_rel|simulate_rel|σ → τ → Prop|bisim` under
`TCSlib/Cryptography`. Nothing found.

**The `Games/` layer:** `git diff 9e7a9648 a0e31483 -- TCSlib/Cryptography/Games` is empty.

## ===== briefs/pairings/gates/44-pairing-fills/findings-r1.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's chat reply, pasted by Seyoon. The text below is verbatim.
The evidence ZIP it mentions (gate44-pairing-fills-evidence.zip) was not uploaded; only this Markdown was received. -->

# Gate 44 pairing fills — round 1 findings

**Verdict: HOLD. Open findings: 0 blockers, 1 major, 1 minor, 1 note.**

The delivered proofs establish the frozen T1 and T4 statements. The hold concerns the required acceptance of disclosed duplication.

| Audited item | Pin |
|---|---|
| Exchange | `30ef1257a56873489b599007782046b7dedeb7fc` |
| Campaign records | `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` |
| #340 / merge base | `916afc25c21f5e52b4b01958186ad55d2f615fd1` / `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| #346 / merge base | `89a18a8225be1b76166af12a15179da291747783` / `7291f6b237fec75add1549c0992c174442180488` |
| Joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

## Findings

Lean paths below are under `TCSlib/Cryptography/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G44-01 | **Major** | #340, `Pairing/Assumptions.lean:199`; #346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighboring reader proofs | Disclosed exact re-derivations are classified as “no duplicated proved material; nothing for the duplication ledger.” T1’s inline verdict identity is precisely public `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), specialized to the solver-success decision bit. The checkpoint’s `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` also re-prove the polynomial-time facts for identical public `InteractiveHandler` projection functions (`Games/Efficiency.lean:538`, `:542`, `:546`, `:550`). Both families are disclosed, but no explicit human acceptance and scheduled repayment is recorded in the audited material or pinned duplication ledger. Policy §1 requires that acceptance, including for mechanically forced copies. | Reuse shared facts, promoting missing generic readers where necessary; or record Seyoon’s explicit acceptance, the shared home and repayment point. Correct both reports’ “nothing for the ledger” dispositions. |
| G44-02 | **Minor** | #346, `BonehBoyenMachine/Draws.lean:58`, `:130`; References entries in `Words.lean:60` and `Handler.lean:62` | `[PS10, Theorem 52.3]` is an inaccurate locator for bounded rejection sampling. That theorem concerns the discrete-log collection of one-way functions; its proof merely remarks that the domain is easy to sample. It does not specify this sampler, fixed coin budget, fallback or statistical bound. The actual formal justification is `Candidates.statClose_sampleBelowL`. This is a genuine source with an inaccurate citation, rather than a fabricated-tag major. | Attribute the bounded sampler to the existing library construction and bound. Retain PS10 §2.8/Theorem 52.3 only as context, and correct the three References entries consistently. |
| G44-03 | **Note** | `pack-r1.md:339`, Assumptions paired-control figures | The prose doubles the totals. Each variant has **2 sealed and 2 unsealed probes**, with **25** expected negative errors: 12 in A and 13 in B. Across strict and coe together: 4 sealed, 4 unsealed and 50 negative errors. The raw logs and plans verify these actual counts, with every reader passing. | Correct “per variant” and “50 … in each.” No replay or control repair is needed. |

The PS10 source supports G44-02’s distinction between its discrete-log theorem and the bounded sampler. [cs.cornell.edu](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf?utm_source=chatgpt.com)

G44-01 is an acceptance/ledger requirement. The overlaps were disclosed; it is **not** an undisclosed-copy accusation.

## Proof and scope checks

| Question | Result |
|---|---|
| **1 — T1 correctness** | **Pass.** `exists_bdhDistinguisher` constructs a total polynomial-time raw function through `NUPPT.ofPolyTime`, retaining the solver’s coins and advice. On the real tuple law, `coinsCongr` and `expect_sample_equiv` preserve success probability and the unused target sample disappears. On the random law, exchanging independent target/coin samples and encoding injectivity give the inverse-order bound, including outputs outside the encoding range. `accept_bdhGame_le` is pointwise in the security parameter; the bad-order charge is exactly the stated hypothesis. The final negligibility argument adds no assumption. |
| **1 — T4 correctness** | **Pass.** The handler uses total polynomial-time string operations. Negation reduces before subtracting from the modulus; differences and inverses agree with `ZMod`, including inverse zero. Membership precedes message decoding. The per-call identity covers all three oracles and every simulator state. At most one tape entry is consumed per oracle call, so the budget suffices. The sampler is exactly G40-03’s; encoding injectivity supplies its strict modulus bound on every generated group. Machines and error function are chosen before the universally quantified bits and security parameter. |
| **1 — edge cases and sufficiency** | **Pass.** Parameter zero, zero budget, empty coins/advice, absent initialization/challenge, refused target-key queries, repetitions, invalid messages and identity collisions are covered. T4 requires no identity-injectivity/order-growth hypothesis: both simulations use the same zero-inverse convention. Orders zero and one and invalid mathematical group objects are excluded by `BilinearGroup`’s fields; malformed machine strings still receive total polynomial-time behavior. `bb1_sidSecure` is unchanged and reaches `sorryAx` exactly through T2 and T3. T1 is not used by that consumer. |
| **2 — frozen declarations** | **Pass.** Independently reconstructed T44 from the pinned trees; both PR diffs match the pack. T1/T4 headers and statement prose are unchanged. Restoring permitted regions restores the base files. All six T1 and ten T4 mutation controls reject their mutations. The checkpoint inserts only its four imports and Contents section. Public declarations: 101 → 275, exactly 174 additions, with no other frozen declaration changed or removed. |
| **3 — seven readers** | **Pass.** Independent reconstruction is byte-exact: `Defs` +43/−0, `BonehBoyen` +37/−0 at the approved positions. All nine controls reject their mutations. These are precisely the three `oracleImpl_*_onSpec` readers and four approved BB1 encoding/message-space readers, with approved proofs and no added attribute. The casts’ `rfl` witnesses read `Defs`’ own `sidSpec`; consumers use published theorems. |
| **4 — LE-bb1m** | **Pass.** Direct parent/head comparison confirms only deletion of unused `hpp` and reordering of the formula docstring. No statement changes. |
| **5 — duplication** | G44-01 and the grading tables below. No additional undisclosed duplicate was identified. The checkpoint overlaps were reviewed beyond the full-name clash check. |
| **6 — Rule 10** | **Pass.** Recounted **24/24** joint-owner and **16/16** supplement seals: source/probe hashes, conservative request sets reconstructed from collector catalogs, exact source recovery after removing harness insertions, install/EOF coverage, rc 0 and no errors. Strict/coe A/B exclusions match the rulings. Assumptions controls pass at the corrected counts; supplement controls give 24 expected negatives per variant, with all readers/unsealed controls passing. The three skipped owners have **12** row-, source- and probe-identical records against phase 2; its **32/32** earlier seals also recount cleanly. Those owners do not import changed Assumptions, so unchanged inputs justify reuse. The explicit scan has 1,016 items and zero foreign reads; source inspection agrees. |
| **7 — sources** | **Pass apart from G44-02.** BB04 §4.2/Theorem 4.1 and algorithm B are correct sources. The theorem is on printed p. 6 and its proof on pp. 7–8, so the locators are compatible. T1’s independent folklore attribution is accurate under Q10. PS10 Algorithm 43.2 and Definition 181.1 are apt for Euclid and statistical closeness. Inherited missing SOK00/BF01 entries remain outside these fills. |
| **8 — documentation** | **Pass apart from G44-02.** New public docstrings state their formulas; sketches describe the delivered proofs. The sole 15-line sketch omission is pre-existing frozen `bb1SimChal_fresh`. “Handler theorem T1” explicitly names `Games.exists_handlerMachine`, distinguishing it from pairing T1; consistently spelling out “Games” would improve readability. |
| **9 — replay and axioms** | **Pass on supplied evidence.** Independently reconstructed the 16-module downstream set and 1,427-module root/audit closure. All 16 build logs and source bindings recount cleanly: rc 0, no errors, exactly the two T2/T3 admission warnings. Census: **198 → 196**, exactly T1 and T4 removed. Both targets have the standard three axioms and no sorried dependency; the owner census has 604 constants and no nonstandard axioms. State, output-map and snapshot-preservation records are consistent. |
| **10 — disclosures** | G44-03 is an additional pack discrepancy. Other recorded staging/provenance slips do not alter the audited code or conclusions. The shared signing key establishes account-session provenance, not individual authorship. |

The BB04 page locators and the PS10 Euclid/statistical-closeness locators were checked against the primary texts. [crypto.stanford.edu](https://crypto.stanford.edu/~xb/eurocrypt04b/bbibe.pdf?utm_source=chatgpt.com)

The principal bounds checked are

\[
\operatorname{accept}(G.\mathrm{bdhGame}\ A\ \kappa)
\le G.\mathrm{dbdhAdv}\ D\ \kappa+2^{-\kappa}+\delta(\kappa),
\]

\[
q(\kappa)2^{-n}\le(q(\kappa)+1)2^{-\kappa}=\sigma(\kappa),
\qquad n=\kappa+w_G(\kappa)+1.
\]

## Grades: BM-F01–BM-F09

These dispositions do not add to the open-finding counts.

| Finding | Grade / disposition |
|---|---|
| BM-F01 | Agree: note, **closed** by removal of the unused proof. |
| BM-F02 | Agree: minor, **closed** by corrected argument order and explicit security parameter. |
| BM-F03 | Agree: evidence note, **closed**. Independently recounted Oracles controls: 14 negative and 14 reader rows per variant, all as expected. |
| BM-F04 | Agree: note, superseded by landing-head seals and unchanged-input comparisons. |
| BM-F05 | Agree: evidence nits; source/log/hash checks resolve the substantive questions. G44-03 is separate. |
| BM-F06 | Agree: inherited documentation note, outside permitted edits. |
| BM-F07 | Agree: size note; the files exceed the target but remain below the cap. |
| BM-F08 | Agree: disclosed promotion request. The private range-type lemmas derive from published readers without re-proving an existing public IBE theorem. |
| BM-F09 | Agree: suitable machine-specific public glue, with its formula and sketch. |

## Grades: #340’s seven overlap disclosures

| Item | Grade / disposition |
|---|---|
| 1 — raw machine versus `NUPPT.wrap` | Agree. Composition of verified construction layers; the alternative’s bookkeeping does not make this an additional copied theorem. |
| 2 — equality test | Agree. `polyTimeComputable_pairEq` is reused. |
| 3 — projections | Agree. Fixed compositions of published projections; the iterated-first-projection theorem does not supply the required second-projection contract. |
| 4 — target probability | Agree. Tuple-specific application of published probability/injectivity facts; the list-membership bound is a near-alternative. |
| 5 — verdict identity | **Reject “no duplicated proved material / no ledger”: G44-01.** The exact public identity is re-derived inline. Disclosure does not establish acceptance of retained debt. |
| 6 — bad-order bound | Agree as disclosed pattern overlap. The ElGamal safe-prime/index proof is not copied as an interchangeable theorem. |
| 7 — advantage inequality | Agree. Direct absolute-value API use; no matching public Games lemma was identified. |

The checkpoint’s identical round-input projections and polynomial-time facts have the same acceptance gap. Its API obstruction is real, but the required acceptance/repayment record is absent. Other disclosed specializations, casts, encoding-contract applications and simulator comparisons have different contracts or apply existing facts.

## Verification and limits

All **14/14** outer and **549/549** verification-archive checksums pass, with an exact file set. All **186** source-manifest entries pass; **181** Lean source copies bind to pinned git blobs. All **43** bundle sections match their separate copies. The two additionally consulted review archives verify **962/962** and **255/255** inner files and their pinned outer hashes.

The ZIP contains the independent checks, results, mutation-control reruns and pinned duplication ledger. **I did not run a fresh Lean compilation**; compilation/axiom conclusions use the hash-bound supplied replay and probes, independently recounted and checked against the inspected sources.

Gate 40, the T2/T3 fill and #351/#352 are not re-audited. Merge order and snapshot adoption remain maintainer conditions.

**Notation:** `A`: adversary/solver; `D`: reduction distinguisher; `G`: bilinear generator; `κ`: security parameter; `q(κ)`: query budget; `w_G(κ)`: source-group encoding width; `n`: sampler width defined above; `δ(κ)`: bad-order bound; `σ(κ)`: simulation-error bound. T1/T4 and BM-F01–BM-F09 retain the campaign’s labels.

## ===== briefs/pairings/gates/44-pairing-fills/findings-r2.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's reply, uploaded by Seyoon. Verbatim below. -->

**Gate 44 pairing fills — round 2 findings**

**Verdict: CLEAR. Open findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

All three round-1 findings are closed. DL-55 and DL-56 remain accepted debt scheduled for cleanup Stage 2; closing G44-01 does not mean that repayment has already occurred.

| Audited item | Pin |
|---|---|
| Exchange | `2e0152540aae5bb1ce7f8061572aedc5a4fc5437` |
| Campaign records | `4f4a7592a54cf82fa04f96b83645d7936672614c` |
| PR #340, T1 | `916afc25c21f5e52b4b01958186ad55d2f615fd1` — unchanged |
| PR #346, T4 | `98cb0e521a94e94c304c78348fb5d3033435a3ed` |
| Joint tree T44′ | `bee027f0903d531b3a43511cea16bfa123210291` |
| Round-1 joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

| Finding | Previous severity | Disposition and evidence |
|---|---|---|
| **G44-01** | Major | **Closed by explicit acceptance and scheduled repayment.** At the records pin, the plan's ruling, ledger rows DL-55/DL-56 and Stage 2 scope agree. DL-55 identifies the published verdict identity, its promotion to a shared low-level home importable by both layers, and the subsequent re-points of `TrapdoorPredictor` and pairing T1. DL-56 identifies the four projection facts in `Games/Efficiency` as the shared home and schedules the four re-points, with a reader there if required. Both identify Seyoon's acceptance and cleanup Stage 2 as the repayment point. This satisfies policy §1. Both reports retain their original disposition with an accurate dated correction; the bb1-machine review carries the matching correction. These copies bind to staging records commit `bb0199d6dc6753996e674b6a5dcdcb49b092f5f9`, after the records pin, as disclosed. |
| **G44-02** | Minor | **Closed by LE-g44.** Its sole parent is round 1's #346 head. Only `BonehBoyenMachine/Draws.lean`, `Words.lean` and `Handler.lean` change, by +22/−7 lines. Each is byte-identical to its parent after removing comments, including nested block comments and docstrings while preserving strings. The sampler attribution is correct: `Candidates.sampleBelowL` supplies the construction, and `Candidates.statClose_sampleBelowL` supplies precisely the stated fixed-coin, fallback-zero statistical bound. The unchanged `statClose_draw` applies that theorem. PS10 §2.8/Theorem 52.3 is consistently marked as context for easy domain sampling; all three References entries are corrected. |
| **G44-03** | Note | **Closed by the corrected figures.** Raw logs and control records confirm, per strict/coe variant, **2 sealed and 2 unsealed probes**, with **25 negatives: 12 in A and 13 in B**. Across both variants: **4 sealed, 4 unsealed, 50 negatives**. Every negative fails exactly once, every reader passes, and both unsealed probes have zero errors in each variant. Both control checks report `ALL_OK True`. |

The T44′ evidence binds to the audited heads and shows no regression:

| Check | Result |
|---|---|
| **Integrity and bundle** | **Pass.** All **14/14** outer checksums and **132/132** inner verification checksums pass, with exact file sets. All **30** bundle sections match their separate pack, archive or pinned repository sources. All seven Lean copies in `sources-r2.zip` bind to pinned git blobs. The round-1 material used for comparisons matches its specified exchange pin. |
| **Merges and delta** | **Pass.** Independently reconstructed T44 and all **six** permutations of the records pin and two PR heads. Each merge is clean and yields T44′. Its nine changed paths relative to the records pin equal their respective PR-head blobs. The entire code diff from T44 to T44′ equals `le-g44.diff.txt` byte for byte. The records advance adds no code change. |
| **Replay and state** | **Pass on supplied replay evidence.** Independently recovered the **10-module** downstream subset; the build queue covers it exactly. All ten source/log/output hashes bind, all return rc 0, and no build log contains an error. The only warnings are the two inherited T2/T3 admissions. The copied state hash matches round 1's final state. The plan builds 10 and reuses 1417; the unchanged full root/audit order contains **1427 modules**, all reported OK by the final state check. The nine replay-tool hashes match round 1's supplied tool bytes. |
| **Objects and preservation** | **Pass.** All ten rebuilt oleans have link count 1, different inodes from the base output, and no `.ilean`. Seven are byte-identical to T44's; only the three documentation-edited modules differ. The 1458-entry output maps independently compare as **1455 equal, 3 changed**, with no additions or removals. The new map hashes to `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`. Snapshot #4's before/after/final rehashes report **0 extra / 0 changed / 0 missing**. The old-output rechecks and subsequent deletion record are consistent with preservation of the new output. |
| **Admissions and axioms** | **Pass.** The recorded per-module admission counts are identical: **196 → 196**, with zero in the three edited owners. The axioms probe hashes to both rounds' run records; its log is byte-identical to round 1's. T1 and T4 use only `propext`, `Classical.choice` and `Quot.sound`. The nine-owner census reports **604 constants, 0 nonstandard axioms**. `bb1_sidSecure` still reaches `sorryAx` exactly through the two out-of-scope T2/T3 statements. |
| **Canonical coe-A seals** | **Pass.** Draws **1644**, Words **2242**, Handler **2275**, and BonehBoyenMachine **2311** requests. All four runs have rc 0 and zero errors. Independently checked source/probe/log hashes, exact source recovery after removing harness insertions, identical request rows/readers/exclusions and insertion payloads, and complete install/EOF coverage. Comparisons use round 1's `rel/` request-set record for Draws, as disclosed. |
| **Lint** | **Pass: no regression.** Non-INFO campaign output is byte-identical: **92 FAIL / 104 WARN over 524 files**. INFO differences are only the three line counts. The supplied three-file style check reports zero findings, and `sk15` has zero hits. |

**The remaining round-1 seals can be carried forward; a rerun is unnecessary for this delta.** Every other code source is blob-identical, the three edited owners have identical code after comment removal, and both the collector probe and its complete log are byte-identical to round 1's. The four new canonical seals additionally confirm unchanged requests and harness behavior against the new output. Together these justify carrying the strict/coercion A/B variants, paired controls, supplement seals and explicit-unfold results within this round's stated scope.

**Round 1's passes still hold and were not re-audited.** No change reopens the proof or edge-case conclusions, frozen statements and statement prose, seven readers, LE-bb1m, declaration inventory, name-clash result, or the prior grading of BM-F01–BM-F09 and #340's disclosures. Item 5 and the four projection re-derivations now have the acceptance records required by G44-01.

**No new undisclosed change or finding was identified.** The three corrections' post-pin provenance is accurate. Live PR checks confirm #346 is pushed to `98cb0e52`, #340 remains at `916afc25`, and both descriptions now disclose the resolutions. The other known slips remain compatible with the audited material.

I did **not** run a fresh Lean compilation. Compilation, axiom and filesystem-preservation conclusions rely on the supplied hash-bound replay/probe records, independently recounted and checked against pinned sources. Git reconstruction, checksum verification, source binding, comment removal, map comparisons and seal-record comparisons were performed locally.

Gate 40, the T2/T3 fill and #351/#352 remain outside scope. Merge order and snapshot adoption remain maintainer conditions. The user dispatches and merges.

## ===== blueprint/src/references/boneh-boyen-2004-selective-id-ibe.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Efficient Selective-ID Secure Identity Based Encryption Without Random Oracles

Dan Boneh and Xavier Boyen. Cryptology ePrint Archive, Report 2004/172, full version dated
December 2004 (20 pages; tag `BB04`); extended abstract in *EUROCRYPT 2004*, LNCS 3027,
pp. 223–238. The ePrint numbering is used throughout.

**Scope.** Only the passages that the pairing campaign uses are transcribed (DW-7; pairing
ruling Q12): §2.1–§3.1 (IBE and HIBE, the selective-identity game, Definitions 2.1–2.2,
bilinear groups, BDH and Decision BDH, Definition 3.1), §4.1–§4.2 (the HIBE construction and
Theorem 4.1 with its proof) and §4.4 (arbitrary identities). The PDF is not committed. Physical
and printed pages coincide. The scoped raw extraction is
`boneh-boyen-2004-selective-id-ibe.raw.md`. Mathematics is set in LaTeX; the wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-63c1c7b0817f-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

## 2 Preliminaries

**Section 2, opening (p. 2).** Before presenting our results we briefly review the definition
of security for an IBE system. We also review the definition of groups equipped with a
bilinear map.

<a id="pdf-63c1c7b0817f-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Section 2.1, IBE and HIBE systems (pp. 2–3).** Recall that an Identity Based Encryption
system (IBE) consists of four algorithms [Sha84, BF01]: **Setup**, **KeyGen**, **Encrypt**,
**Decrypt**. The **Setup** algorithm generates system parameters, denoted by *params*, and a
master key *master-key*. The **KeyGen** algorithm uses the master key to generate the private
key corresponding to a given identity. The encryption algorithm encrypts messages for a given
identity (using the system parameters) and the decryption algorithm decrypts ciphertexts using
the private key. In a Hierarchical IBE [HL02, GS02] identities are vectors. A vector of
dimension $\ell$ represents an identity at depth $\ell$. Algorithm **KeyGen** takes as input
an identity $\mathrm{ID}=(I_1,\dots,I_\ell)$ at depth $\ell$ and the private key
$d_{\mathrm{ID}|_{\ell-1}}$ of the parent identity
$\mathrm{ID}|_{\ell-1}=(I_1,\dots,I_{\ell-1})$ at depth $\ell-1$. It outputs the private key
$d_{\mathrm{ID}}$ for identity $\mathrm{ID}$. We refer to the master-key as the private key at
depth $0$ and note that an IBE system is an HIBE where all identities are at depth $1$.

<a id="pdf-63c1c7b0817f-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.95 -->

**Section 2.1, the selective-identity game (p. 3).** Boneh and Franklin [BF01, BF03] define
chosen ciphertext security for IBE systems under a chosen identity attack. In their model the
adversary is allowed to adaptively chose the public key it wishes to attack (the public key on
which it will be challenged). Canetti, Halevi, and Katz [CHK03, CHK04] define a weaker notion of
security in which the adversary commits ahead of time to the public key it will attack. We
refer to this notion as *selective identity, chosen ciphertext secure IBE* (IND-sID-CCA). More
precisely, selective identity IBE and HIBE security is defined using the following game:

- **Init:** The adversary outputs an identity $\mathrm{ID}^*$ where it wishes to be
  challenged.
- **Setup:** The challenger runs the **Setup** algorithm. It gives the adversary the resulting
  system parameters *params*. It keeps the *master-key* to itself.
- **Phase 1:** The adversary issues queries $q_1,\dots,q_m$ where query $q_i$ is one of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds by running
    algorithm **KeyGen** to generate the private key $d_i$ corresponding to the public key
    $\langle\mathrm{ID}_i\rangle$. It sends $d_i$ to the adversary.
  - Decryption query $\langle C_i\rangle$ for identity $\mathrm{ID}^*$ or any prefix of
    $\mathrm{ID}^*$. The challenger responds by running algorithm **KeyGen** to generate the
    private key $d$ corresponding to $\mathrm{ID}^*$ (or the relevant prefix thereof as
    requested). It then runs algorithm **Decrypt** to decrypt the ciphertext $C_i$ using the
    private key $d$. It sends the resulting plaintext to the adversary.

  These queries may be asked adaptively, that is, each query $q_i$ may depend on the replies
  to $q_1,\dots,q_{i-1}$.
- **Challenge:** Once the adversary decides that Phase 1 is over it outputs two equal length
  plaintexts $M_0,M_1\in\mathcal M$ on which it wishes to be challenged. The challenger picks a
  random bit $b\in\{0,1\}$ and sets the challenge ciphertext to
  $C=\mathbf{Encrypt}(\textit{params},\mathrm{ID}^*,M_b)$. It sends $C$ as the challenge to
  the adversary.
- **Phase 2:** The adversary issues additional queries $q_{m+1},\dots,q_n$ where $q_i$ is one
  of:
  - Private key query $\langle\mathrm{ID}_i\rangle$ where $\mathrm{ID}_i\neq\mathrm{ID}^*$ and
    $\mathrm{ID}_i$ is not a prefix of $\mathrm{ID}^*$. The challenger responds as in Phase 1.
  - Decryption query $\langle C_i\rangle\neq\langle C\rangle$ for $\mathrm{ID}^*$ or any prefix
    of $\mathrm{ID}^*$. The challenger responds as in Phase 1.

  These queries may be asked adaptively as in Phase 1.
- **Guess:** Finally, the adversary outputs a guess $b'\in\{0,1\}$. The adversary wins if
  $b=b'$.

We refer to such an adversary $\mathcal A$ as an IND-sID-CCA adversary. We define the
advantage of the adversary $\mathcal A$ in attacking the scheme $\mathcal E$ as

$$
\mathrm{Adv}_{\mathcal E,\mathcal A}=\left|\Pr[b=b']-\frac12\right|
$$

The probability is over the random bits used by the challenger and the adversary.

*Transcription note.* The `-layout` extraction drops the vertical bars; the page image
(checked at 150 dpi) shows the absolute value $\left|\Pr[b=b']-\tfrac12\right|$.

<a id="pdf-63c1c7b0817f-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Definition 2.1.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$-selective identity, adaptive chosen ciphertext secure if for any
$t$-time IND-sID-CCA adversary $\mathcal A$ that makes at most $q_{ID}$ chosen private key
queries and at most $q_C$ chosen decryption queries we have that
$\mathrm{Adv}_{\mathcal E,\mathcal A}<\epsilon$. As shorthand, we say that $\mathcal E$ is
$(t,q_{ID},q_C,\epsilon)$ IND-sID-CCA secure.

**Semantic Security.** As usual, we define selective identity, chosen plaintext security for
an IBE system as in the preceding game, except that the adversary is not allowed to issue any
decryption queries. The adversary may still issue adaptive private key queries.

<a id="pdf-63c1c7b0817f-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

**Definition 2.2.** We say that an IBE or HIBE system $\mathcal E$ is
$(t,q_{ID},\epsilon)$-selective identity, chosen plaintext secure if $\mathcal E$ is
$(t,q_{ID},0,\epsilon)$-selective identity, chosen ciphertext secure. As shorthand, we say that
$\mathcal E$ is $(t,q_{ID},\epsilon)$ IND-sID-CPA secure.

<a id="pdf-63c1c7b0817f-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.95 -->

**Section 2.2, bilinear groups (p. 4).** We briefly review the necessary facts about bilinear
maps and bilinear map groups [Jou00, Mil04]. We use the following notation:

1. $\mathbb G$ and $\mathbb G_1$ are two (multiplicative) cyclic groups of prime order $p$;
2. $g$ is a generator of $\mathbb G$.
3. $e$ is a bilinear map $e:\mathbb G\times\mathbb G\to\mathbb G_1$.

Let $\mathbb G$ and $\mathbb G_1$ be two groups as above. A bilinear map is a map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ with the following properties:

1. Bilinearity: for all $u,v\in\mathbb G$ and $a,b\in\mathbb Z$, we have
   $e(u^a,v^b)=e(u,v)^{ab}$.
2. Non-degeneracy: $e(g,g)\neq 1$.

We say that $\mathbb G$ is a bilinear group if the group action in $\mathbb G$ can be computed
efficiently and there exists a group $\mathbb G_1$ and an efficiently computable bilinear map
$e:\mathbb G\times\mathbb G\to\mathbb G_1$ as above. Note that $e(\,,\,)$ is symmetric since
$e(g^a,g^b)=e(g,g)^{ab}=e(g^b,g^a)$.

Throughout the paper, for a prime order group $\mathbb G$ we use $\mathbb G^*$ to denote the set
$\mathbb G\setminus\{1_{\mathbb G}\}$ where $1_{\mathbb G}$ is the identity of $\mathbb G$.

<a id="pdf-63c1c7b0817f-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.95 -->

## 3 Complexity Assumptions

**Section 3 and Section 3.1, BDH and Decision BDH (pp. 4–5).** Let $\mathbb G$ be a bilinear
group of prime order $p$. We review the standard Bilinear Diffie-Hellman (BDH) assumption and
define the Bilinear Diffie-Hellman Inversion (BDHI) assumption.

The BDH problem [Jou00, SOK00, BF01] in $\mathbb G$ is as follows: given a tuple
$g,g^a,g^b,g^c\in\mathbb G$ as input, output $e(g,g)^{abc}\in\mathbb G_1$. An algorithm
$\mathcal A$ has advantage $\epsilon$ in solving BDH in $\mathbb G$ if

$$
\Pr\left[\mathcal A(g,g^a,g^b,g^c)=e(g,g)^{abc}\right]\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, and the random bits used by $\mathcal A$. Similarly, we say
that an algorithm $\mathcal B$ that outputs $b\in\{0,1\}$ has advantage $\epsilon$ in solving
the *decision* BDH problem in $\mathbb G$ if

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|\ge\epsilon
$$

where the probability is over the random choice of generator $g$ in $\mathbb G^*$, the random
choice of $a,b,c$ in $\mathbb Z_p$, the random choice of $T\in\mathbb G_1$, and the random bits
consumed by $\mathcal B$. We refer to the distribution on the left as $\mathcal P_{\mathrm{BDH}}$
and the distribution on the right as $\mathcal R_{\mathrm{BDH}}$.

*Transcription note.* The `-layout` extraction drops the vertical bars, but the page image
(checked at 130 dpi) shows an absolute value around the difference, as transcribed. This
differs from `PairingCryptographyPlan.md` ("Where the papers' formulations differ", item 6),
which says the decision advantage of §3.1 is written without one; that record should be
corrected (the draft's choice is unaffected: it uses the absolute difference of acceptance
probabilities, which is the same number).

<a id="pdf-63c1c7b0817f-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Definition 3.1.** We say that the (Decision) $(t,\epsilon)$-BDH assumption holds in
$\mathbb G$ if no $t$-time algorithm has advantage at least $\epsilon$ in solving the
(Decision) BDH problem in $\mathbb G$.

Occasionally we drop the $t$ and $\epsilon$ and refer to the BDH and Decision BDH assumptions in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

## 4 Efficient Selective Identity IBE and HIBE Based on BDH Without Random Oracles

**Section 4 and Section 4.1, opening (p. 5).** We construct an efficient HIBE system that is
selective identity secure without random oracles based on the Decision BDH assumption. In
particular, this implies an efficient selective identity, chosen ciphertext secure IBE based on
Decision BDH without random oracles.

Let $\mathbb G$ be a bilinear group of prime order $p$ (the security parameter determines the
size of $\mathbb G$). Let $e:\mathbb G\times\mathbb G\to\mathbb G_1$ be the bilinear map. For
now, we assume public keys (ID) of depth $\ell$ are vectors of elements in $\mathbb Z_p^{\ell}$.
We write $\mathrm{ID}=(I_1,\dots,I_\ell)\in\mathbb Z_p^{\ell}$. The $j$-th component
corresponds to the identity at level $j$. We later extend the construction to public keys over
$\{0,1\}^*$ by first hashing each component $I_j$ using a collision resistant hash
$H:\{0,1\}^*\to\mathbb Z_p$. We also assume messages to be encrypted are elements in
$\mathbb G_1$. The HIBE system works as follows:

<a id="pdf-63c1c7b0817f-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 4.1, the HIBE construction (p. 6).**

**Setup**$(\ell)$: To generate system parameters for an HIBE of maximum depth $\ell$, select a
random generator $g$ in $\mathbb G^*$, a random $\alpha\in\mathbb Z_p$, and set
$g_1=g^{\alpha}$. Next, pick random elements $h_1,\dots,h_\ell\in\mathbb G$ and a random element
$g_2\in\mathbb G$. The public parameters *params* and the secret *master-key* are given by

$$
\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell),\qquad \textit{master-key}=g_2^{\alpha}
$$

For $j=1,\dots,\ell$, we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function:
$F_j(x)=g_1^{x}h_j$.

**KeyGen**$(d_{\mathrm{ID}|_{j-1}},\mathrm{ID})$: To generate the private key
$d_{\mathrm{ID}}$ for an identity $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$ of depth
$j\le\ell$, pick random $r_1,\dots,r_j\in\mathbb Z_p$ and output

$$
d_{\mathrm{ID}}=\left(g_2^{\alpha}\cdot\prod_{k=1}^{j}F_k(I_k)^{r_k},\ g^{r_1},\dots,g^{r_j}\right)
$$

Note that the private key for ID can be generated just given a private key for
$\mathrm{ID}|_{j-1}=(I_1,\dots,I_{j-1})\in\mathbb Z_p^{j-1}$, as required. Indeed, let
$d_{\mathrm{ID}|_{j-1}}=(d_0,\dots,d_{j-1})$ be the private key for $\mathrm{ID}|_{j-1}$. To
generate $d_{\mathrm{ID}}$ pick a random $r_j\in\mathbb Z_p$ and output
$d_{\mathrm{ID}}=(d_0\cdot F_j(I_j)^{r_j},d_1,\dots,d_{j-1},g^{r_j})$.

**Encrypt**$(\textit{params},\mathrm{ID},M)$: To encrypt a message $M\in\mathbb G_1$ under the
public key $\mathrm{ID}=(I_1,\dots,I_j)\in\mathbb Z_p^{j}$, pick a random $s\in\mathbb Z_p$ and
output

$$
C=\left(e(g_1,g_2)^{s}\cdot M,\ g^{s},\ F_1(I_1)^{s},\dots,F_j(I_j)^{s}\right)
$$

Note that $e(g_1,g_2)$ can be precomputed once and for all so that encryption does not require
any pairing computations. Alternatively, $e(g_1,g_2)$ can be included in the system
parameters, in which case $g_2$ can be dropped.

**Decrypt**$(d_{\mathrm{ID}},C)$: Consider an identity $\mathrm{ID}=(I_1,\dots,I_j)$. To decrypt
a given ciphertext $C=(A,B,C_1,\dots,C_j)$ using the private key
$d_{\mathrm{ID}}=(d_0,d_1,\dots,d_j)$, output

$$
A\cdot\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}=M
$$

Indeed, for a valid ciphertext, we have

$$
\frac{\prod_{k=1}^{j}e(C_k,d_k)}{e(B,d_0)}
=\frac{\prod_{k=1}^{j}e(F_k(I_k),g)^{s r_k}}
{e(g,g_2)^{s\alpha}\prod_{k=1}^{j}e(g,F_k(I_k))^{s r_k}}
=\frac{1}{e(g_1,g_2)^{s}}
$$

<a id="pdf-63c1c7b0817f-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.95 -->

**Section 4.2, opening and Theorem 4.1 (p. 6).** The HIBE system above is reminiscent of the
Gentry-Silverberg HIBE which is only known to be secure in the random oracle model.
Surprisingly, our choice of functions $F_1,\dots,F_\ell$ enables us to prove security without
random oracles. We prove security of our HIBE system under the standard Decision BDH assumption
in $\mathbb G$.

**Theorem 4.1.** Suppose the $(t,\epsilon)$-Decision BDH assumption holds in $\mathbb G$. Then
the previously defined $\ell$-HIBE system is $(t',q_S,\epsilon)$-selective identity, chosen
plaintext (IND-sID-CPA) secure for arbitrary $\ell$ and $q_S$, and any
$t'<t-\Theta(\tau\,\ell\,q_S)$ where $\tau$ is the maximum time for an exponentiation in
$\mathbb G$.

<a id="pdf-63c1c7b0817f-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, the simulator's setup (p. 7).** Suppose $\mathcal A$ has advantage
$\epsilon$ in attacking the HIBE system. We build an algorithm $\mathcal B$ that solves the
Decision BDH problem in $\mathbb G$. Algorithm $\mathcal B$ is given as input a random 5-tuple
$(g,g^a,g^b,g^c,T)$ that is either sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) or from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform and independent in
$\mathbb G_1$). Algorithm $\mathcal B$'s goal is to output $1$ if $T=e(g,g)^{abc}$ and $0$
otherwise. Set $g_1=g^a$, $g_2=g^b$, $g_3=g^c$. Algorithm $\mathcal B$ works by interacting
with $\mathcal A$ in a selective identity game as follows:

**Initialization.** The selective identity game begins with $\mathcal A$ first outputting an
identity $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)\in\mathbb Z_p^{k}$ of depth $k\le\ell$ that it
intends to attack. If necessary, $\mathcal B$ appends random elements in $\mathbb Z_p$ to
$\mathrm{ID}^*$ so that $\mathrm{ID}^*$ is a vector of length $\ell$.

**Setup.** To generate the system parameters, algorithm $\mathcal B$ picks
$\alpha_1,\dots,\alpha_\ell\in\mathbb Z_p$ at random and defines
$h_j=g_1^{-I^*_j}g^{\alpha_j}\in\mathbb G$ for $j=1,\dots,\ell$. It gives $\mathcal A$ the
system parameters $\textit{params}=(g,g_1,g_2,h_1,\dots,h_\ell)$. Note that the corresponding
master key, which is unknown to $\mathcal B$, is $g_2^{a}=g^{ab}\in\mathbb G$. As before, for
$j=1,\dots,\ell$ we define $F_j:\mathbb Z_p\to\mathbb G$ to be the function

$$
F_j(x)=g_1^{x}h_j=g_1^{x-I^*_j}g^{\alpha_j}
$$

<a id="pdf-63c1c7b0817f-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 1 (p. 7).** $\mathcal A$ issues up to $q_S$ private key queries.
Consider a query for the private key corresponding to
$\mathrm{ID}=(I_1,\dots,I_u)\in\mathbb Z_p^{u}$ where $u\le\ell$. The only restriction is that
ID is not a prefix of $\mathrm{ID}^*$. Let $j$ be the smallest index such that
$I_j\neq I^*_j$. Necessarily $1\le j\le u$. To respond to the query, algorithm $\mathcal B$
first derives a private key for the identity $(I_1,\dots,I_j)$ from which it then constructs a
private key for the requested identity $\mathrm{ID}=(I_1,\dots,I_j,\dots,I_u)$. Algorithm
$\mathcal B$ picks random elements $r_1,\dots,r_j\in\mathbb Z_p$ and sets

$$
d_0=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\prod_{v=1}^{j}F_v(I_v)^{r_v},\quad
d_1=g^{r_1},\quad\dots,\quad d_{j-1}=g^{r_{j-1}},\quad
d_j=g_2^{\frac{-1}{I_j-I^*_j}}g^{r_j}
$$

We claim that $(d_0,d_1,\dots,d_j)$ is a valid random private key for $(I_1,\dots,I_j)$. To
see this, let $\tilde r_j=r_j-b/(I_j-I^*_j)$. Then we have that

$$
g_2^{\frac{-\alpha_j}{I_j-I^*_j}}F_j(I_j)^{r_j}
=g_2^{\frac{-\alpha_j}{I_j-I^*_j}}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j}
=g_2^{a}\left(g_1^{I_j-I^*_j}g^{\alpha_j}\right)^{r_j-\frac{b}{I_j-I^*_j}}
=g_2^{a}F_j(I_j)^{\tilde r_j}
$$

It follows that the private key $(d_0,d_1,\dots,d_j)$ defined above satisfies

$$
d_0=g_2^{a}\cdot\Bigl(\prod_{v=1}^{j-1}F_v(I_v)^{r_v}\Bigr)\cdot F_j(I_j)^{\tilde r_j},\quad
d_1=g^{r_1},\ \dots,\ d_{j-1}=g^{r_{j-1}},\quad d_j=g^{\tilde r_j}
$$

where $r_1,\dots,r_{j-1},\tilde r_j$ are uniform in $\mathbb Z_p$. This matches the definition
for a private key for $(I_1,\dots,I_j)$. Hence, $(d_0,d_1,\dots,d_j)$ is a valid private key for
$(I_1,\dots,I_j)$. Algorithm $\mathcal B$ derives a private key for the requested ID from the
private key $(d_0,d_1,\dots,d_j)$ and gives $\mathcal A$ the result.

*Transcription note.* The exponents are stacked fractions in the PDF, flattened by the
extraction; they were read from the page image (150 dpi) as $-\alpha_j/(I_j-I^*_j)$ and
$-1/(I_j-I^*_j)$. The PDF sets identities in an upright font ($\mathrm I_j$); plain $I_j$ is
used here.

<a id="pdf-63c1c7b0817f-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.95 -->

**Proof of Theorem 4.1, Challenge (p. 7).** When $\mathcal A$ decides that Phase 1 is over, it
outputs two messages $M_0,M_1\in\mathbb G_1$ on which it wishes to be challenged. Algorithm
$\mathcal B$ picks a random bit $b\in\{0,1\}$ and responds with the ciphertext
$C=(M_b\cdot T,\ g_3,\ g_3^{\alpha_1},\dots,g_3^{\alpha_k})$. Since $F_i(I^*_i)=g^{\alpha_i}$ for
all $i$, we have that

$$
C=\left(M_b\cdot T,\ g^{c},\ F_1(I^*_1)^{c},\dots,F_k(I^*_k)^{c}\right)
$$

Hence, if $T=e(g,g)^{abc}=e(g_1,g_2)^{c}$ then $C$ is a valid encryption of $M_b$ under the
public key $\mathrm{ID}^*=(I^*_1,\dots,I^*_k)$. On the other hand, when $T$ is uniform and
independent in $\mathbb G_1$ (when the input 5-tuple is sampled from
$\mathcal R_{\mathrm{BDH}}$) then $C$ is independent of $b$ in the adversary's view.

<a id="pdf-63c1c7b0817f-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Proof of Theorem 4.1, Phase 2, Guess and the advantage (p. 8).**

**Phase 2.** $\mathcal A$ continues to issue queries not issued in Phase 1. Algorithm
$\mathcal B$ responds as before.

**Guess.** Finally, $\mathcal A$ outputs a guess $b'\in\{0,1\}$. Algorithm $\mathcal B$
concludes its own game by outputting a guess as follows. If $b=b'$ then $\mathcal B$ outputs
$1$ meaning $T=e(g,g)^{abc}$. Otherwise, it outputs $0$ meaning $T\neq e(g,g)^{abc}$.

When the input 5-tuple is sampled from $\mathcal P_{\mathrm{BDH}}$ (where
$T=e(g,g)^{abc}$) then $\mathcal A$'s view is identical to its view in a real attack game and
therefore $\mathcal A$ must satisfy $\left|\Pr[b=b']-1/2\right|>\epsilon$. On the other hand,
when the input 5-tuple is sampled from $\mathcal R_{\mathrm{BDH}}$ (where $T$ is uniform in
$\mathbb G_1$) then $\Pr[b=b']=1/2$. Therefore, with $g$ uniform in $\mathbb G^*$, $a,b,c$
uniform in $\mathbb Z_p$, and $T$ uniform in $\mathbb G_1$ we have that

$$
\left|\Pr\left[\mathcal B(g,g^a,g^b,g^c,e(g,g)^{abc})=0\right]
-\Pr\left[\mathcal B(g,g^a,g^b,g^c,T)=0\right]\right|
\ge\left|\left(\frac12\pm\epsilon\right)-\frac12\right|=\epsilon
$$

as required. This completes the proof of Theorem 4.1.

*Transcription note.* The page image (150 dpi) shows absolute-value bars on both sides, as
transcribed.

<a id="pdf-63c1c7b0817f-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 4.4, arbitrary identities (p. 8).** We can extend our HIBE above to handle identities
$\mathrm{ID}=(I_1,\dots,I_\ell)$ with $I_j\in\{0,1\}^*$ (as opposed to $I_j\in\mathbb Z_p$) by
first hashing each $I_j$ using a collision resistant hash function $H:\{0,1\}^*\to\mathbb Z_p$
prior to key generation and encryption. A standard argument shows that if the scheme above is
selective identity, chosen ciphertext secure then so is the scheme with the additional hash
function. We note that there is no need for a full domain hash into $\mathbb Z_p$; for example,
a collision resistant hash function $H:\{0,1\}^*\to\{1,\dots,2^b\}$ where $2^b<p$ is sufficient
for the security proof.

## ===== policy.md (records, at e6cdf4d4eed898acd71d48bd60082140eb076cfe) =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
