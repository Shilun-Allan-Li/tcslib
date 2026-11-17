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
