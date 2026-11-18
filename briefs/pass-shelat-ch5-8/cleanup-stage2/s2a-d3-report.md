# Cleanup Stage 2, S2-A batch D3 (A30 rest, A37): report

**Status:** D3 is done in-house. It finishes S2-A's 16 open rows: A30's last 9 and all 7 of A37.
- **On the branch:** `cleanup/stage2-s2a` has 2 new signed commits, pushed fast-forward. No PR is open, and nothing
  else changed.
- **Code checks:** the replay, the admissions, decls2 and the `rfl` probes are all clean.
- **Seals:** coe-A and coe-B give 0 errors on `Factoring`, `GoldreichLevin` and `RSA`. `FromPermutation`, downstream,
  keeps only job J3's residue, which is the same on D2's tree.
- **Lint:** one new finding (Q-D3-1).
- **Rows still open in S2-A:** only S2-SL-214, partly done and held under Q-D2-1.

Evidence is in `$SP/s2a-d3/`, where `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
Its `SHA256SUMS` file covers 408 files and has SHA-256
`35e6dcf7607ac1af71ac687225229a62b43b4a9e7404f1bebda32e2416ece064`.

| Pin | Value |
|---|---|
| Base (S2-A) | `61a5f0fb640622c15fdd33df56efa470b2bf26c8` |
| D2 head (D3 start) | `a1545eae990f82918ad4e344428e38668ab911ed` |
| Branch head | **`dff281b53746377cd72e57c3aeeadf3d1f59a332`** (`origin/cleanup/stage2-s2a`) |
| Records | `687accf3` (D2's records and decision row, committed by the coordinator) |
| Inputs | `s2a-workplan-r1.md`, `s2a-items.tsv` rows of A30/A37, the S2-A rulings, the D3 dispatch |

## 1. Commits (one per step, `git commit -S`, staged by explicit path, the two trailer lines)

| Step | Commit | Files (+/−) | Rows |
|---|---|---|---|
| A37 GoldreichLevin | `316083129cd1ac3a6deaf2482b039f9c78509d04` | `HardCorePermutation/GoldreichLevin` +51 −20 | S2-BO-064..069, S2A-N07 |
| A30 Factoring (rest) | `dff281b53746377cd72e57c3aeeadf3d1f59a332` | `Candidates/Factoring` +187 −79 | S2-BO-111..117, 119, 121 |

- **Totals:** 2 files, +238 / −99 since D2's head; 62 files, +1,578 / −860 since the S2-A base.
- **Signatures:** both commits carry an SSH `gpgsig` header. `git verify-commit` cannot check them here (no allowed
  signers file), as in D1 and D2.
- **Order:** A37 was committed before A30's rest. A30's first part is D2's `ecd35ee99`.
- **Amend:** the A30 commit was amended once before the push, re-signed, to re-wrap one docstring line over 100
  characters.

**What changed:**
- **A37 (`GoldreichLevin`):**
  - **S2A-N07:** a private reader, `oddParam_eval : oddParam.eval m = m + m + 1`.
  - **`oddCoins` body (Q-A2):** the coins of `A` at `2m + 1` are read at `oddParam.eval m`, and the one-bit prefix at
    `(const 1).eval m`. Both go through `Equiv.arrowCongr (finCongr _)`.
  - **`ofFn_oddCoins` (Q8, the planned header):** the coins are `c ∘ Fin.cast (congrArg A.coinLen (oddParam_eval m))`.
  - **The four consumers:** they read the run back through `NUPPT.runAt_eq`, `List.ofFn_congr` and
    `ofFn_arrowCongr_finCongr`.
  - **`runAt_wrap`:** it is given its length equation as `PolyExpr.eval_const`.
- **A30 (`Factoring`):**
  - **Bodies (Q-A2):** the `fmult` body casts along `((const 2).mul var).eval n = 2n`, and `plantFactor` tries with
    `fmult.f n` read at `2n` bits.
  - **Headers:** `fmult_f`, `fmult_inv_factor` and the private `fac_prodInverter_eq_yaoB` are restated as planned (Q8).
  - **Consumers:** they read the blocks, the challenges, the answers and the round coins at `2n` bits through
    `fmult_inLen` and `fmult_outLen`. The four consumers are `fmult_easy`, `fac_weak_key`, `exists_plantFactorer` and
    `fac_strong_key`.
  - **Proof sketches:** those of `fac_strong_key`, `exists_plantFactorer` and Theorem 36.3 are updated.

## 2. Checks

| Check | Result |
|---|---|
| Per-step file checks (`lean_check_tree.sh`, one Lean process) | `GoldreichLevin` and its 3 direct importers; `Factoring` and its 2 direct importers (`Candidates`, `RSA`): all rc 0, 0 errors, no `sorry` |
| Development seals before each commit | coe-A and coe-B 0 errors on `GoldreichLevin` (B: 8 at D2's head) and `Factoring` (B: 24 at D2's head) |
| **D3 replay** | `$SP/olean-replay-s2a-d3`, a `cp -al` copy of D2's output (D2's tree kept intact as the parent). See the next table |
| Admissions (`sorryscan.py`, full order) | `TOTAL 192 in 44 modules; native_decide 0; axiom 0`, byte-identical to D2's |
| decls2 vs D2 head | 2 CHANGED: `fmult_f` (S2-BO-117) and `fmult_inv_factor` (S2-BO-119); nothing added or removed |
| decls2 vs base `61a5f0fb` | 38 ADDED, 15 CHANGED, 4 REMOVED, which is D2's list plus those 2 CHANGED. All are ruled |
| Private declarations (not tracked by decls2) | `fac_prodInverter_eq_yaoB` header (S2-BO-112), `ofFn_oddCoins` header (S2-BO-069), `oddParam_eval` added (S2A-N07) |
| Q-A2 `rfl` probes (`qa2/`, unsealed, on the D3 tree) | 3/3: `fmult = fmult_d1`; `plantFactor = plantFactor_d1`, with the D2 body over `fmult_d1`; `oddCoins = oddCoins_d1` |
| Q-A2 negative controls | `QA2FCtl` and `QA2GLCtl` fail with Type mismatch |

The D3 replay used `stateplan` from D2's checked state at `dff281b5`, with `downorder` and `fullorder`:

| Check | Result |
|---|---|
| Changed modules | 2 |
| Queue | 178 to build, 1,269 reused |
| `permod` | 178 modules; rc≠0 0; `error:` 0; `error(` 0; `sorry` 0 |
| `stateplan update`, then `check` over the 1,447-module order | 178 taken; RESULT OK |
| Link counts | 178 rebuilt at link count 1; 1,269 reused, all hard links |
| Output map | 1,478 entries, SHA-256 `68099201c42f53067c39b9b96098420e709c0453f44c099ddde81186df088470` |
| Output map vs D2's map | changed only `Factoring` and `GoldreichLevin` |
| `NthRootLemmas` overlay | `c0a9cff0…` |
| Snapshot #10 rehash (`$SP/olean-snapshot-10`) | 0/0/0 before, after the copy, after the replay and at the end |
| D2 tree rehash | byte-identical map before, after the copy, after the replay and at the end |
| D3 tree rehash | byte-identical map after the seals |

**How the probes were built:**
- **`QA2F.lean`** imports `Factoring` and copies the two D2-head bodies verbatim, under the suffix `_d1`.
- **`QA2GL.lean`** is a copy of the head `GoldreichLevin.lean` with the D2-head `oddCoins` body inserted. The copy is
  needed because `oddCoins` is private.

**Seals at the head** (`seal/d3/`, D3 tree, the archived instrumenter unmodified, gated runner):
- **Owners:** `Factoring` and `GoldreichLevin`, plus their consumers downstream, `RSA` and
  `Pseudorandom/Generators/Asymptotic/FromPermutation`. The facades have no declarations.

| Owner | coe-A base → D2 → D3 | coe-B base → D2 → D3 |
|---|---|---|
| `Candidates/Factoring` | 0 → 0 → **0** | 22 → 24 → **0** |
| `HardCorePermutation/GoldreichLevin` | 0 → 0 → **0** | 8 → 8 → **0** |
| `Candidates/RSA` | 0 → 0 → 0 | 3 → 0 → 0 |
| `Generators/Asymptotic/FromPermutation` | D2 tree 2 → D3 2 | D2 tree 19 → D3 19 |

**The `FromPermutation` residue is job J3's, not S2-A's:**
- **Declarations** (`tools/errdecl.py`):
  - coe-A: `exists_owpPredictorSnoc`;
  - coe-B: `iterPRG`, `iterPRG_eq_expand`, `cor_81_7`, `exists_owpPredictorSnoc`, `owpGenPRG`,
    `owpGenPRG_G_castSucc/_last/_outEquiv`, `owpGenPRG_outEquiv(_ofFn)` and `owp_hardcore_prg`.
- **Rows:** these are exactly scope rows S2-SL-313..315 and S2-BO-002, 009, 155..163, all with job **J3**.
- **Not caused by D3:** the same two probes run on D2's tree give the same errors, line for line
  (`seal/d3-on-d2tree/`).

**Lints** (`lint/`):
- **`style_lint` on the 2 files:** `GoldreichLevin` 0 findings.
  - `Factoring`: the size finding was already there, now 1,916 lines (it was 1,808).
  - **One new finding:** `fac_prodInverter_eq_yaoB`'s proof grew to 27 lines with no **Proof sketch.** (Q-D3-1).
- **`campaign_style_lint --check8b`:** FAIL 25/92 and WARN 389/105, unchanged. Only these INFO/WARN line counts change:
  - `Factoring` 1,807 → 1,915;
  - `GoldreichLevin` 854 → 885, and 10 → 11 private declarations.
- **Line width:** every added line is at most 100 characters.

## 3. Deviations and judgment calls (none adds a public declaration or changes a statement beyond the ruled ones)

1. **`ofFn_oddCoins`.** Under seal B, `wrapCoinsEquiv_symm_ofFn` would not unify with metavariable arguments, so it is
   applied with its arguments given.
   - **Prefix cast:** the cast of the one-bit prefix is stated with `show 1 + _ = (const 1).eval m + _`, not as a
     `congrArg` beta-redex.
2. **`fmult` body.** It names the length equation with a term-mode `have h : ((const 2).mul var).eval n = 2 * n`, as
   the plan allows ("or `fmult_inLen`/`fmult_outLen`", which are stated after the definition and cannot be used in it).
3. **`fac_strong_key` (S2-BO-113).** The planned proof-only fix needed a real transport, not a one-line cast.
   - **What was removed:** the D2 proof identified the family-length inverter with `prodInverter A n` by defeq (`hB`),
     and `invProbOpt_le_invProb` is no longer used here.
   - **What replaces it:** a local bound, about 45 lines. The inversion event at the family's lengths is reindexed
     block-wise to `2n` bits, using `Equiv.piCongrRight`, `uprob_comp_equiv` and `uprob_mono`. The challenge encodings
     are compared through `FunFamily.ofFn_blocks_symm`, and the answer through `NUPPT.inverter_eq_some_iff` and
     `FunFamily.ofFn_blocks`.
   - **Rest of the proof:** it runs with `fm`, which is `f_mult` read at `2n` bits, the same function as in the
     `plantFactor` body.
4. **`exists_plantFactorer` (S2-BO-111).** It adds four local reindexings, `yB`, `cc`, `htry` and `hround`:
   - the padded inverter, the challenge and the round coins are read at `2n` bits;
   - one try at `2n` bits is the family-length try read back, through `yaoTry_eq`, `Function.update` and
     `prodFun_apply`.
5. **Size.** A30's rest is +187/−79 lines, against the plan's ~70 for the whole step. `Factoring` was already over
   1,000 lines and is now 1,915.

## 4. Helpers and duplication

- **New declarations:** only S2A-N07 (`oddParam_eval`, private, planned). There are no new public declarations.
- **Local `have`s:** `hv`, `ec`, `hrun` (GoldreichLevin); `hx₀`, `hY` (twice, with different statements), `hpad`,
  `hv`, `yB`, `cc`, `htry`, `hm`, `E`, `hinv`, `hb` (Factoring). Each is a cast-specific reading through published
  lemmas.
- **The `hv : (var + var).eval m = m + m` pair:**
  - **Where:** in `glHalf_invProbAt_even` and `glHalf_predProb_even`, two lines each.
  - **Why no helper:** factoring it out would add an unplanned declaration.
- **Searches** (nothing equivalent exists):
  - `rg "theorem \w*(blocks|padTrue|yaoTry|yaoB|prodFun)\w*"`: no cast lemma for `padTrue`, `blocks` or `yaoTry`.
  - `rg "(PolyExpr.add .var .var).eval|eval_double"`: no reader for `var + var`.
  - The `invProb`/`invProbOpt` lemma list: no transport of `invProbOpt` along input/output equivalences.
- **Re-proofs:** no inline derivation re-proves a public TCSlib or Mathlib fact.

## 5. Items left

None of D3's 16 rows. In all of S2-A, only S2-SL-214 is still open (partial), held under Q-D2-1 as instructed.
- **Held:** Q-D2-1, Q-D2-3, Q-D2-4, Q-D2-5 and Q-D2-6 wait for Seyoon's rulings.
- **Trees:** none deleted. `$SP/olean-replay-s2a-d1`, `$SP/olean-snapshot-10` and `$SP/olean-replay-s2a-d2` are
  intact. `$SP/olean-replay-s2a-d3` is kept for adoption.
- **Deleted:** my scratch (the D3 dev tree and the probe directories).
- **Free disk:** about 3.0 GB.

## 6. Questions for Seyoon (recommended option first)

- **Q-D3-1. The new missing proof sketch on `fac_prodInverter_eq_yaoB`** (27 lines; S2-BO-112's proof grew in A30).
  - **(a) Recommended:** add it to the docstring-only commit of Q-D2-3 (a), with the other four sketches.
  - (b) Add it now, as its own docstring-only commit with a small incremental replay.
  - (c) Leave it for Stage 3.
- **Q-D3-2. `Factoring` grew by 108 lines** (now 1,915; it was already over the 1,000-line limit).
  - **(a) Recommended:** queue its split for Stage 3 with the other size splits (Q-D2-3), with no change now.
  - (b) Record a justification in the decision log instead of a split.

**Ready to run** — S2-A's code rows are complete at `dff281b5`. The remaining S2-A decisions are the held rulings
(Q-D2-1, Q-D2-3..6) and Q-D3-1/2.
