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
