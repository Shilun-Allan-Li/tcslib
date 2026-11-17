# Fill `bb1-machine`: T4 `exists_bb1_distinguisher` (the BB1 reduction machine) — NOT FINISHED, scope request

In-house fill job, 2026-11-16 UTC, under the overnight authorization (Codex audits later). `$SP` =
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. Paths below are relative to this
directory unless they start with `$SP`.

**Status: T4 is still `sorry`.** The Gate 40 route (G40-03 and the T4 section) is built and checked up to the last
step. A complete proof of T4 exists and checks under the development seals A and B with the standard axioms only,
but it needs **seven readers added to two frozen files** (`IdentityBased/Defs.lean`: 3; `IdentityBased/BonehBoyen.lean`:
4). The brief says: "No other frozen file changes (stop and report the exact scope request if needed)". The
permission classifier also refused edits to those files, and that refusal was not worked around. The branch
therefore stops at a commit where everything compiles with T4 still `sorry`. There are no private stand-in
statements and nothing was weakened. The scope request, with the readers' exact statements and the ready T4 proof,
is under **Scope request** below and in `scope-request/`.

Rules followed:
- `python3 -I` throughout; `PATH=$HOME/.elan/bin:$PATH`; Lean 4.25.0; no `lake` command and no cache get.
- Lean ran only through:
  - `scripts/lean_check_tree.sh`, for builds (`tools-used/review/runner.py` via `run-dev-build.sh`);
  - LE-gate40's `runner_full.py` (`lean -DmaxErrors=0 <probe>`, no `-o`), for the collector, seals, controls, scan
    and axioms;
  - `tools-used/devcheck.sh` and `tools-used/dev/dct.sh`, for development and the scope-request probes (no `-o`).
- Only `$SP/dl-oleans` was used; it is exclusive to this job and is restored (see Tree). `dl-oleans-2` was not
  touched.
- One Lean process of this job ran at a time.
- The only processes stopped were this job's own: a seal run made stale by a docstring fix, killed by recorded PID
  (`$SP/bb1m-work/pids-seal-run.txt`; its partial outputs were discarded).
- `/home/user/tcslib` was only read. Nothing was pushed.

## Commits

- Worktree `$SP/wt-fill-bb1-machine` (sparse: `TCSlib/`, `audits/`, `scripts/`, lake files, `lean-toolchain`,
  `policy.md`, `TCSlib.lean`). Local branch `fill/bb1-machine` from `9e7a96481785d6cac4dea3b2e990c49ac278b060` (the
  #331 head), independent of T1's branch.
- Three signed checkpoint commits (`gpgsig` SSH header present on each; local verification is not possible here, since
  no `allowedSignersFile` is configured). Trailers as instructed. Details in `git/`.
  - `c158b66e49bf69cf77e0edc8a523df14332a0616` "bb1-machine: checkpoint (drawn exponents; handler, Init round; T4 still sorry)"
  - `8dc69cdae7a8a6541d4ebe3297272847c7b318b4` "bb1-machine: checkpoint (handler rounds and run; reduction lemmas; T4 still sorry)"
  - `7c0a55e0239c14786612d0cd4462e64238543ca1` (HEAD) "bb1-machine: checkpoint (split the handler's string layer; facade imports; T4 still sorry)"
- The final message `bb1-machine: prove the BB1 reduction machine (T4)` was **not** used, because T4 is not proved.
- Diff vs `9e7a9648`: 5 files, +2240 lines (`git/diffstat.txt`). One owned file is modified and four helper modules are
  new. No other file changes.

## What changed

- **`BonehBoyenMachine.lean` (owned).**
  - Added: four imports of the helper modules and a `## Contents` section in the module docstring. The campaign lint
    requires this, because the file is now the facade of `BonehBoyenMachine/`.
  - Byte-identical to the base: T4's header, statement prose, `**Proof sketch.**` and body (`sorry`). The sketch is
    not rewritten, since no proof is delivered.
- **New helper modules** under `IdentityBased/BonehBoyenMachine/`, imported only by `BonehBoyenMachine.lean`. Each has
  a module docstring: title, Main definitions, Main results, References [BB04, §4.2] and [PS10].
  - **`Draws.lean`** (451 lines; 28 public, 1 private):
    - lengths: `qLen`, `aLen` (with `_zero`, `_one`, `_two` and `_eval`); `blockLen` (`n = κ + wG + 1`);
    - the draw: `draw` (`draw_eq`), `order_le_two_pow`, `statClose_draw`;
    - the simulator with the exponent as an argument: `drawStep`, with case lemmas `drawStep_zero`,
      `drawStep_one_none`, `_one_target`, `_one_key`, `_two_none`, `_two_repeat`, `_two_fresh`, `_two_invalid`;
    - `exists_drawStep_eq_pure`, `exists_simulate_tape_eq_pure`, `abs_expect_draws_sub_le`.
  - **`Words.lean`** (632 lines; 125 public, 0 private): the handler's string functions, each with an `_eq` reader and
    a polynomial-time lemma.
    - Lengths: `aWidth`, `nn`.
    - Round-input readers: `rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `zD`, …, `zT`, `sJ`, `sO1`, `sR`, `sCom`, `sChal`,
      `sC`, `sO2`, `kT`, `kA`.
    - Residues: `pS`, `modS`, `negS`, `addS`, `mulS`, `invS`. Group operations: `mulGS`, `powGS`. The drawn exponent:
      `blkS`, `uS`.
    - Values: `rU_input`, …, `zD_of`, …, `listToNat_modS`, …, `listToNat_invS`, `listToNat_pS`, `mulGS_ofFn`,
      `powGS_ofFn`, `mulT_ofFn`, `memT_ofFn`, `memT_headD`, `order_lt_aWidth`, `listToNat_natToList_val`,
      `idToZ_padFin`, `uS_of_blkS`.
  - **`Handler.lean`** (899 lines; 7 public, 71 private):
    - public: `handler` (a `Games.PolyHandler 3 (qLen G ℓ) (aLen G ℓ)`), `handler_seedLen`, `handler_advInput`,
      `handler_result`, `seedBlocks`, `seedBlocks_window`, `simulate_handler`;
    - private: the answers; the round function `runF` and its polynomial time; the state encoding; the round lemmas
      `runF_zero`, `runF_one`, `runF_two`, `handler_impl_stEnc`.
  - **`Reduction.lean`** (243 lines; 6 public, 1 private): `runAccept` (with `runAccept_eq`,
    `runAccept_eq_zero_or_one`), `expect_handlerMachine`, `expect_castImpl_freshImpl`, `abs_expect_runAccept_sub_le`.
- **Conventions.**
  - 166 public declarations added, none removed or changed (`statements/`). Each has a formula docstring.
  - Every proof of 15 lines or more (counting the declaration) has a `**Proof sketch.**` (`tools-used/dev/sk15.py`:
    none missing).
  - No `@[simp]`, `sorry` or `native_decide` in the new modules. Widths are at most 100.
- **Sizes.** `Handler.lean` is 899 lines and `Words.lean` 632: above the 600-line target, below the 1000 cap. The
  handler was split once; its string layer went to `Words.lean`.

## Route (Gate 40, G40-03 and the T4 section)

1. **Draws.**
   - `n = κ + wG(κ) + 1` (`blockLen`).
   - `draw G κ d w = (sampleBelowL p (Nat.size p) n n ⟦w⟧).getD 0`, on `n²` coin bits per draw.
   - `p ≤ 2^{wG} < 2^n` (`order_le_two_pow`, by injectivity of `encG`) and `statClose_sampleBelowL` give
     `statClose_draw`: each draw is within `(1/2)^n` of uniform.
2. **The handler** (`Words`, `Handler`): the paper's algorithm `B`, working on encodings only.
   - Group operations come from `Ops` (`mulG`, `powG`, `mulT`, `memT`, `orderStr`).
   - Residues come from `ArithmeticFP` (`divModStr`, `subStr`, `addStr`, `mulStr`). The inverse uses `xgcdStr`, with
     `0 ↦ 0`.
   - The `j`-th query takes its exponent from block `j` of the seed (`uS`, `seedBlocks`).
   - The state `⟨1^j, ⟨o_1, o_2⟩⟩` is padded to a fixed length.
   - `simulate_handler`: the handler's run is the run of `drawStep` on the tape `j ↦ draw (block j)`. Proved with
     `simulate_eq_of_abs_bounded` and the round lemmas.
3. **T1.** `A'` comes from `Games.exists_toCompOn_of_toComp A`, and `Games.exists_handlerMachine` gives the machine.
   `expect_handlerMachine`: that machine accepts the Decision BDH string with probability
   `𝔼_ρ 𝔼_V runAccept ρ (draw ∘ V)`.
4. **Ideal exponents.**
   - `expect_castImpl_freshImpl`: the simulator with fresh exponents per query, on the game's lengths (`castImpl`),
     accepts with probability `𝔼_U runAccept ρ U` (`expect_simulate_castImpl_toCompOn`,
     `ETTGame.expect_simulate_tapeImpl`).
   - `abs_expect_runAccept_sub_le`: the two acceptance probabilities differ by at most `q(κ) · (1/2)^n`
     (`abs_expect_draws_sub_le`, `OneWay.statClose_pi`).
   - `q · (1/2)^n ≤ (q + 1) · 2^{−κ} = σ(κ)`.
5. **Glue (blocked).**
   - Needed: call by call, `bb1SimImpl` has the law of `castImpl (freshImpl drawStep)` (private `expect_bb1SimImpl`,
     in `scope-request/MachineProbe*.lean.txt`).
   - With it, T4 follows from `advantage_eq`, `accept_eq`, `bb1SimGame_eq` and `BilinearGen.dbdhGame_eq`, then
     `abs_expect_sub_le` four times, with `σ κ = (q + 1)(κ) · 2⁻¹^κ`.
   - This step reads `IBEScheme.oracleImpl` at the game's query types, and reads `bb1Scheme`'s encodings `encPP` and
     `encSK`, its `MsgSpace`, and `bb1SimCt`. Under the seals, no published reader allows any of these.

## Scope request (the exact obstruction)

**Why the published API is not enough**

| What is needed | Published API | Why it fails under the seals |
|---|---|---|
| Evaluate `S.oracleImpl κ init key chal i x s` with `x : (S.sidSpec κ).dom i` (the game's query type) | `oracleImpl_zero`, `_one`, `_two` | They are stated with `x : Fin (S.idLen.eval κ) → Bool`. Unifying the two needs `S.inLens κ i =?= S.idLen.eval κ`, but `inLens` is sealed. A cast of `x` cannot be put back in the argument slot. |
| Read `bb1Scheme`'s encodings (`encPP`, `encSK`, `bb1SimCt`) and its message space | the generated `bb1Scheme_*` `simps` lemmas | They state the lengths literally and the parameters as `Sigma` types. Rewriting with them gives a motive that is not type-correct at `Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool`. Anonymous constructors `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` do not elaborate. |

The type equations `(S.sidSpec κ).dom i = …` and `.rng i = …` are **not** needed from the owners. Consumers derive
them from the published `IBEScheme.sidSpec_eq`, `bitSpec_dom`, `bitSpec_rng`, `inLens_*` and `outLens_*`, as
`MachineProbeMin` does.

**Minimal request: seven readers.** Each one is `rfl` or one line for the owner.

| # | Where | Reader |
|---|---|---|
| 1–3 | `IdentityBased/Defs.lean`, namespace `IBEScheme`, after `oracleImpl_two` | `oracleImpl_zero_onSpec`, `oracleImpl_one_onSpec`, `oracleImpl_two_onSpec` |
| 4–5 | `IdentityBased/BonehBoyen.lean`, after the `simps` attribute of `bb1Scheme` | `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK` |
| 6 | same place | `bb1Scheme_msgSpace_iff` |
| 7 | `IdentityBased/BonehBoyen.lean`, after `bb1SimCt_eq` | `ofFn_bb1SimCt` |

1–3. `oracleImpl_zero_onSpec` (and the `_one`, `_two` versions for `key`/`chal`):
   ```lean
   theorem oracleImpl_zero_onSpec {σ : Type} (κ : ℕ) (init …) (key …) (chal …)
       (x : (S.sidSpec κ).dom 0) (s : σ) :
       S.oracleImpl κ init key chal 0 x s =
         (init (cast (show (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) from rfl) x) s).bind
           fun p => .pure (cast (show (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)
             from rfl).symm p.1, p.2) :=
     (OracleComp.bind_pure _).symm
   ```
4. `ofFn_bb1Scheme_encPP G ℓ κ d pp`:
   `List.ofFn ((bb1Scheme G ℓ).encPP κ ⟨d, pp⟩) =
   List.ofFn (padFin ((bb1Scheme G ℓ).ppLen.eval κ) (d ++ ⟦g⟧ ++ ⟦g_1⟧ ++ ⟦g_2⟧ ++ ⟦h⟧))`, proved by `rfl`.
5. `ofFn_bb1Scheme_encSK G ℓ κ d k`:
   `List.ofFn ((bb1Scheme G ℓ).encSK κ ⟨d, k⟩) =
   List.ofFn (padFin ((bb1Scheme G ℓ).skLen.eval κ) (⟦d_0⟧ ++ ⟦d_1⟧))`, proved by `rfl`.
6. `bb1Scheme_msgSpace_iff G ℓ κ d pp m`:
   `(bb1Scheme G ℓ).MsgSpace κ ⟨d, pp⟩ m ↔ ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m`, proved by
   `exists_congr fun _ => List.ofFn_inj.symm`.
7. `ofFn_bb1SimCt G ℓ κ d Z T α₁ m`:
   `List.ofFn (bb1SimCt G ℓ κ d Z T α₁ m) = List.ofFn (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
   (⟦decodeT (padFin _ ⟦m⟧) * T⟧ ++ ⟦Z⟧ ++ ⟦Z ^ α₁.val⟧))`, proved by `rw [padFin_ofFn]; rfl`.

The exact Lean text is in `scope-request/BB1ReadersMin.lean.txt`.

**Optional alternative.** `scope-request/BB1Readers.lean.txt` adds the six type equations `sidSpec_dom_*` and
`sidSpec_rng_*` (each `rfl`) and states 1–3 with them. That makes 13 readers.

**Checks of both forms** (logs in `scope-request/logs/`):

| Probe | Natively | Development seal A | Development seal B |
|---|---|---|---|
| `PlProbe/BB1ReadersMin` (built through `lean_check_tree.sh`) | rc 0, 0/0 errors | — | — |
| `PlProbe/BB1Readers` | rc 0, 0 errors | — | — |
| `PlProbe/MachineProbeMin`: the T4 statement, verbatim, proved from the 7 readers, published readers and this fill's modules | rc 0, 0 errors; `#print axioms exists_bb1_distinguisher` = `[propext, Classical.choice, Quot.sound]` | rc 0, 0 errors (2289 definitions sealed), same axioms | rc 0, 0 errors (2290 definitions sealed), same axioms |
| `PlProbe/MachineProbe` (13-reader form) | rc 0, 0 errors | rc 0, 0 errors | rc 0, 0 errors |

`devseal.py` seals every imported TCSlib definition; this is not the canonical seal, which would run on the owners
once the readers land.

**How to finish once the readers land** (a sketch, not done):
1. Move `expect_bb1SimImpl` and `abs_inner_le` from `MachineProbeMin` into a helper module (or `Reduction.lean`).
2. Replace T4's body with the probe's proof, and rewrite the `**Proof sketch.**` to it.
3. Re-run this evidence. `bb1_sidSecure` would then inherit `sorryAx` only from T2 and T3.

## Checks

| Check | Result | Evidence |
|---|---|---|
| Native build (`lean_check_tree.sh`) | At HEAD `7c0a55e0`: the 4 helper modules, the owned file and everything downstream (`BonehBoyenSecurity`, facades `IdentityBased`, `AdvancedEncryption`, root `TCSlib`), 9 modules. All rc 0, `error:` 0, `error(` 0. `sorry` warnings only in `BonehBoyenMachine` (T4) and `BonehBoyenSecurity` (T2, T3), as at the base. Sources bound to `git show HEAD` (9/9). The upstream pairing closure was built from `9e7a9648` sources first: 94 modules, rc 0, 0/0 errors. | `checks/native-final.tsv`, `dev-build/final3/`, `dev-build/base/` |
| Statements | `decls2.py` vs `9e7a9648`: 166 public declarations ADDED, none removed or changed. `touched.py`: T4 UNCHANGED, 239 declarations in new files. | `statements/` |
| Frozen header | `frozen_check_bb1m.py`: reverting only the 4 helper imports and the `## Contents` section gives the base file byte for byte (T4 unchanged): PASS. Controls: 8/8 FAIL as required (T4 header, T4 statement, T4 prose, module docstring, foreign import, unknown helper import, added declaration, Main results). No file outside the owned file and the new helpers is changed. | `frozen/` |
| Admissions | No `sorry`, `admit`, `native_decide`, `@[simp]` or `axiom` in the new modules. `sorry` counts as at the base: 1 (T4), 2 (T2, T3). | `admissions/census.txt` |
| Axioms | Census probe over all 329 constants of the 5 owners: only `exists_bb1_distinguisher` has a non-standard axiom (`sorryAx`). `#print axioms`: T4 and `bb1_sidSecure` include `sorryAx`; `simulate_handler`, `expect_handlerMachine` and `abs_expect_runAccept_sub_le` use `[propext, Classical.choice, Quot.sound]`. The required "T4 standard only; `bb1_sidSecure` inheriting only T2/T3" is **not met** (T4 unproved). The T4 proof in `MachineProbeMin` is standard-only. | `axioms/` |
| Rule 10 seals | Changed owners `Draws`, `Words`, `Handler`, `Reduction`, `BonehBoyenMachine`, with LE-gate40 tools verbatim (`rule10_b.sh`). Strict A/B and coe A/B (coe A canonical): 20/20 rc 0, `error:` 0, `error(` 0, install and EOF records present. Requests (strict A): 1645, 2241, 2274, 2308, 2309. Terms: 40, 46, 99, 47, 5. | `rule10/seals-*.tsv`, `rule10/seal-runs/`, `rule10/seals*/` |
| Paired controls | `mkctl_bb1m.py` = `mkctl_pbdh.py` plus 13 rows: `inLens`, `outLens`, `tupleStr`, `idToZ`, `PolyHandler.input`, `ETTGame.tapeImpl`, and this fill's `qLen`, `draw`, `sJ`, `kT`, `blkS`, `uS`, `handler` (the helper definitions foreign to later helpers). Strict and coe both `ALL_OK True`: 16 control probes per harness, 204 expected sealed failures per harness, each sealed negative fails exactly once, readers pass, all unsealed pass. Unsealed pretest of the new rows: rc 0. | `rule10/ctlcheck-*.log`, `rule10/controls-*`, `rule10/pretest/` |
| Explicit-unfold scan | 628 items: THEOREM 433, OWNED_DEFINITION 86 (each in its own file: Handler 59, Words 26, Draws 1), LOCAL_OR_UNRESOLVED 109 (hypotheses, and published lemmas the scanner leaves unresolved). **0 foreign.** No helper unfolds another helper's definitions: `Handler` reads `Words` only through its `_eq` readers. | `scan/` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography --check8b`, base and head both 92 FAIL / 103 WARN. Non-INFO line sets identical; only the file count changes, 396 → 400. `style_lint.py` on the 5 files: 0 findings. Widths: 0 lines over 100. | `lint/` |
| Tree | Restored: 73 backups put back (0 hash failures); 28 new oleans deleted (incl. the `PlProbe` ones). snapshot-post = snapshot-pre = `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (SNAPSHOT EQUAL). restoreplan: extra 0, changed 0, missing 0. Second snapshot equal. Backups then deleted. | `tree/`, `restore/`, `restore-runner.out` |

Development runs (not evidence, nothing written to the tree): `dct.sh` / `devseal.py` checks of every helper during
development. All helper modules passed the development seals A and B at the final sources.

## Overlap and reuse

Searches: `overlap/search.log`. No published lemma is restated; the helpers reuse the published layers (Route).
Disclosed overlaps of definition or pattern, and near-alternatives:

1. **Round-input readers** (`Words.lean`).
   - Same bodies as published readers:
     - `BB1Machine.rU`, `rZ`, `rW`, `rS` = `Games.InteractiveHandler.rU`, `rZ`, `rW`, `rS` (`Games/Efficiency.lean`,
       already in the closure);
     - `sJ` = `InteractiveHandler.rCnt`;
     - `rS`, `rX` = `LamportMachine.state`, `message` (`Authentication/Signatures/Lamport/Machine.lean`), which have
       `_eq`, `_poly` and `_input` lemmas on `PolyHandler.input`.
   - Why not reused:
     - The `InteractiveHandler` `_input` lemmas are for the other round layout `⟨s, ⟨⟨1^i, x⟩, L⟩⟩`, and of its
       `_eq` readers only `rAns_eq` is published. Under Rule 10, its readers therefore cannot be evaluated on a
       `PolyHandler.input`.
     - The Lamport readers would bring the signature layer into the pairing closure for two one-line readers, and do
       not cover `z`, `ω` or `1^i`.
   - `Games` publishes no readers for `PolyHandler.input`. The body `pairFstD (pairFstD w)` also appears as
     `HardCoreGL.fx` and `ProdEval.u`, for other layouts.
2. **Residue arithmetic** (`modS`, `negS`, `addS`, `mulS`, `invS` and `listToNat_modS`, …, `listToNat_invS`).
   - The same compositions of `ArithmeticFP` with `divModStr`/`xgcdStr` occur privately in `DiscreteLogHardcore.lean`
     (`dlb_rem`, `dlb_invMod`), `RSA.lean` and `Rabin.lean`.
   - Near-alternative: the published `FromDiscreteLog.modularDifference`, which computes `(a + (m − b)) mod m`. Not
     used for `ID − ID*`: it is correct only for `b < m` (the identity numerals are not reduced), and it would bring
     the hashing layer into the closure.
   - The value lemmas are assembled from the published `divModStr_pairEncode`, `xgcdStr_pairEncode`,
     `listToNat_subStr`, `listToNat_addStr`, `listToNat_mulStr`, `ZMod.val_natCast` and `ZMod.neg_val'`.
3. **Group operations on encodings** (`mulGS_ofFn`, `powGS_ofFn`, `mulT_ofFn`, `memT_ofFn`, `listToNat_pS`). These
   restate the `Ops` contract fields (`mulG_spec`, …, `orderStr_spec`) on `G.group κ (G.desc κ r)`, by
   `BilinearGen.inst_eq`. `Pairing/Operations.lean` publishes no such form.
4. **Drawn exponents** (`Draws.lean`).
   - `draw` follows the sampler pattern of `Candidates.expSampleRaw` and `Candidates.ddhExpo`.
   - `statClose_draw` is the published `statClose_sampleBelowL` with `p ≤ 2^{wG} < 2^n`. Its analogue for the DDH
     index layout is `ddhExpo_statClose`. `order_le_two_pow` has no published counterpart.
   - `poly_uS` follows the proof of `Candidates.polyTimeComputable_expSampleRaw` (the host `rejectBlocksL` and
     `natToList_zero_append_drop`). The lemma itself does not apply, because the layout differs.
5. **`drawStep`** restates the answers of the published simulator handlers `bb1SimInit`, `bb1SimKeyQ` and
   `bb1SimChal`.
   - Differences: the exponent is an argument, and the answers are words (`padFin` of the encodings) instead of
     `encPP`, `encSK`, `bb1SimCt`. The published handlers draw their exponents inside, and their answers cannot be
     read under the seals.
   - Its case lemmas mirror `bb1SimInit_none`, …, `bb1SimChal_invalid`. Proving the two agree, call by call, is
     exactly the glue that needs the requested readers.
6. **Reused, not redefined:**
   - tapes: `ETTGame.tapeImpl`, `tapeImpl_apply`, `freshImpl`, `expect_simulate_tapeImpl`; `AdaptiveCPA.extTape`,
     `extTape_of_lt`;
   - casts and T1: `Games.castImpl`, `expect_simulate_castImpl_toCompOn`, `exists_toCompOn_of_toComp`,
     `exists_handlerMachine`, the `PolyHandler` readers; `simulate_eq_of_abs_bounded`;
   - expectations: `expect_sample_equiv`, `expect_sample_comm`, `Bridge.expect_sample_pair`, `prob_sample_eq_uprob`;
   - `OneWay.statClose_pi` (not the zero-knowledge copies); `FunFamily.blocks`.
   - `exists_simulate_tape_eq_pure` has no published analogue.
7. **Private one-liners.**
   - `expect_sample_eq_uprob` (`𝔼 Φ = Pr[Φ = 1]` for `{0,1}`-valued `Φ`): `prob_sample_eq_uprob` plus
     `prob_eq_expect`.
   - `ite_ofFn_one`: inline core `simp`. The related `decide_singleton_eq_true` (`TrapdoorPredictor.lean`) states a
     different identity and is outside the closure.

No duplicated proved material; nothing for the duplication ledger.

> **Correction (2026-11-17, Gate 44 G44-01).** The line above is kept as filed, but its disposition is wrong for
> disclosure 1. `poly_rU`, `poly_rZ`, `poly_rW` and `poly_rS` (`BonehBoyenMachine/Words.lean:261–271`) re-prove the
> polynomial-time facts of the public `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` (`Games/Efficiency.lean:538–550`):
> `BB1Machine.rU`, …, `rS` have the bodies of the `InteractiveHandler` projections, and the four proofs are the same
> compositions. Disclosure 1 records the API obstruction (no published `_eq`
> readers for those projections under Rule 10), but not an acceptance. Seyoon accepted the debt on 2026-11-17:
> it is ledger row **DL-56** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`), repaid in cleanup Stage 2
> (`cleanup-stages.md`): re-point the four to the `Games/Efficiency` facts, adding a reader there if the obstruction
> needs one (proof-only). Resolution: `briefs/pairings/gates/44-pairing-fills/resolutions-r1.md`.

## Limits

- T4 is unproved pending the scope request; see above.
- The canonical seals and controls cover the five changed owners. The downstream `BonehBoyenSecurity` has unchanged
  sources and was only built (rc 0).
- The scope-request probes were checked natively and under the development seals, not under the canonical seal
  machinery: their readers live in a probe module, not in the owners.
- The commits' SSH signatures could not be verified locally.

## Tools (`tools-used/`)

- **Copied unmodified:**
  - from fill-pair-bdh's `tools-used/`: `fullorder.py`, `stateplan.py`, `restoreplan.py`, `permod.py`,
    `restore_derand.sh`, `snapshot.py`, `review/runner.py`, `backup_cum.py`, `backup_g40m.py`, `devcheck.sh`,
    `frozen_check.py`, `frozen_controls.py`;
  - `seal/`: LE-gate40's `tools/`, plus `mkctl_pbdh.py`.
- **New here:**
  - `frozen_check_bb1m.py`, `frozen_controls_bb1m.py`;
  - `seal/review/mkctl_bb1m.py` (its header states the change);
  - `dev/`: `dct.sh`, `dc.sh`, `devseal.py`, `sk15.py`.
- **Drivers:** `run-dev-build.sh`, `rule10_bb1m.sh`, `run-checks.sh` (whole evidence run, output `run-checks.out`),
  `run-scope-min.sh`, `finish-restore.sh`.
- **Inputs:** `work/` holds the build queues and the closure plan. `order/order.txt` is the union of the queues
  (restoreplan's order).

`SHA256SUMS` lists every file here except itself.
