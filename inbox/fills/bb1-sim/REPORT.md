# Fill `bb1-sim` — checkpoint 1 (Claude lead)

Checkpoint 1 of the fill (brief *Checkpoints*):
- the ten approved readers are inserted, and the insertion check with controls passes;
- every helper module's statements elaborate at the check tree;
- decls2 and the StmtDump are run;
- the clash scan is run;
- the outline below maps T2's and T3's chains to the helper lemmas.

The proofs of `expect_simulate_rel` and `expect_sample_rel` are complete (no `sorry`). T2's and T3's bodies are written against the helper statements and elaborate. 17 helper proofs are still `sorry` (listed under *Admissions*). The final replaces this report.

## Bases

| | commit | tree |
|---|---|---|
| issue base (#346 head) | `89a18a8225be1b76166af12a15179da291747783` | |
| records tip at issue | `ca129d64cd54a92aabe517e5262058664b49f651` | |
| **patch base** | `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c` | `b5a5842dd0a5af86975864b29065bec44758f561` |
| **check base** (+ #340 head `916afc25…`) | `7cfe2b1b9a7e001d9ae972811cf85a332518111d` | `02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d` |

`tools/mkbase.sh` output (`evidence/logs/mkbase.log`):
```
PATCH_BASE 72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c tree b5a5842dd0a5af86975864b29065bec44758f561
CHECK_BASE 7cfe2b1b9a7e001d9ae972811cf85a332518111d tree 02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d
```

**Rebase (Q9).** At this checkpoint the records branch is at `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` ("Records: bb1-sim T2/T3 fill dispatched"):
- #346 (`89a18a82…`) is **not** merged, so no rebase was done;
- #340 (`916afc25…`) is not merged either;
- `git diff --stat ca129d64… 8f888790… -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean` is empty.

**Branches** (local, unsigned):
- `fill/bb1-sim` head `35c780c4876b54ddaaf1cbb44c66bac55b23e9e1`;
- check branch `check/bb1-sim-merged` head `a52641d57d361eb9b8b4782dacf986d6623f9e80`, which is the fill commits cherry-picked onto the check base.

`git merge-tree --write-tree 916afc25… 35c780c4…` gives `48a81d43babbdeabed000397657a0d6a512c870f`, equal to the check head's tree.

**Commits** (work in progress; the final series replaces them):
1. `23614c0a` the ten approved readers;
2. `3f430cae` `expect_simulate_rel` and `expect_sample_rel`;
3. `bcb9bcca` the helper modules;
4. `35c780c4` T2's and T3's bodies.

## Environment

The preflight is in `evidence/logs/preflight.log`:
- 4 CPUs.
- Memory: cgroup v1 limit `9223372036854771712` (none). The headroom is `MemAvailable` = 15.19 GiB.
- Disk: the clone's filesystem (ext4) had 14.09 GiB free.
  - Before the preflight I removed this host's own finished statement-job worktrees and olean trees: 6.10 GiB were free before.
  - No dependency tree was copied, moved or deduplicated.

The cache step:
- **Archive store:** 2,420 files (121 MB) were already there, from this host's earlier jobs (`evidence/logs/cache-store.log`).
- **Fetch:** narrowed `lake exe cache get` with the pack's 94 roots (equal to `roots.txt`). It downloaded nothing, decompressed 2,339 files and exited 0 (`cache-get.log`; a first attempt failed only because `lake` was not on `PATH`, and is recorded).
- **Packages:** every present package matches the manifest (`pkgcheck-post.log`: `PACKAGES-CHECK PASS`). There are 0 empty oleans.

**Bootstrap** (`evidence/build/bootstrap/`): `order.txt` at the check base, 193 modules.
- rc 0 for all, 0 errors in both forms, every source bound to `git show HEAD`.
- `sorry` warnings: exactly `base-sorries.txt`, 22 in 10 modules.
- Peak memory 2.9 GiB; 578 s.

## Who did what

- **Lead:**
  - the readers, `Relational`, `Lazy`, `Real`, `Random`, `Chain`, and T2/T3;
  - the checkpoint's checks.
- **Sub-agent A (`stepM`)** is proving `Coupling.lean` (step M) in its own worktree (`/home/user/fill/wt-subA`) and olean tree (`treeA`).
  - The tree was seeded from the lead's tree for 198 modules with byte-identical sources (`evidence/subagents/stepM/seed-treeA.txt`).
  - It shares the one-Lean lock.
  - It runs no `lake` and commits nothing.

## Changed files (lines at patch base → head)

| file | base | head |
|---|---|---|
| `Games/Relational.lean` | 134 | 146 |
| `IdentityBased/Defs.lean` | 476 | 563 |
| `IdentityBased/BonehBoyen.lean` | 714 | 760 |
| `IdentityBased/BonehBoyenSecurity.lean` | 170 | 214 |
| `BonehBoyenSecurity/Lazy.lean` (new) | — | 297 |
| `BonehBoyenSecurity/Real.lean` (new) | — | 296 |
| `BonehBoyenSecurity/Coupling.lean` (new) | — | 187 |
| `BonehBoyenSecurity/Random.lean` (new) | — | 94 |
| `BonehBoyenSecurity/Chain.lean` (new) | — | 102 |

## Checks at this checkpoint

- **Sweep at the check head** (`evidence/build/checkpoint1-sweep/`). The 13 `DOWN` modules and the 5 helpers, in order (`evidence/build/order-head.txt` puts the helpers before `BonehBoyenSecurity`):
  - 18/18 rc 0, 0 errors in both forms;
  - sources bound to `git show HEAD` 18/18;
  - `sorry` warnings 17, all in helper proofs (*Admissions*).
- **Reader insertion check** (`evidence/headers/insertion/`, `run_insertion.sh`, adapted from T4's):
  - `CHECKS 25/25 PASS`, `RESULT PASS`;
  - removing the blocks restores `4e220ead…` and `da875140…` byte for byte;
  - each block is verbatim after its anchor;
  - final hashes `97ecb6e0…` (563 lines) and `88454d6f…` (760 lines).

  The 12 controls give `ALL_CONTROLS_OK True`:
  - unmutated: PASS;
  - one character in a reader: FAIL, exactly one differing line;
  - a reader deleted: FAIL, MISSING;
  - an extra line in either file: FAIL;
  - a reader moved or reordered: FAIL, MOVED;
  - a docstring edited: FAIL;
  - a reader duplicated: FAIL.
- **decls2** against the patch base (`evidence/decls2/decls2-checkpoint1.tsv`): **ADDED 59 = the ten readers + 49 helper declarations, 0 CHANGED, 0 REMOVED.**
- **StmtDump** (`evidence/stmtdump/`): 65 constants (the 59 new ones, the four targets, `prob_simulate_rel`, `bb1_sidSecure`) with full names and types; 0 missing, 0 errors.
- **Clash scan** (`evidence/clash/checkpoint1/`): 59 new names, 0 CLASH, 0 DUP-NEW, 0 same-short-name rows.
- **Development seal A** (`devseal.py`, the probe's; not evidence): `Lazy`, `Real`, `Random`, `Chain` and `BonehBoyenSecurity` all give rc 0 and 0 errors. The canonical seals come at the final.

## Admissions at this checkpoint

`Relational`, `BonehBoyenSecurity`, `Defs` and `BonehBoyen` have no `sorry`. The 17 helper `sorry`s:
- `Lazy`: `bb1SimImpl_two_of_not`, `bb1SimImpl_two_fresh_allOutputs`, `bb1SimImpl_allOutputs_of_ne_two`, `expect_simulate_bb1SimLazy`.
- `Real`: `setup_out`, `sidImpl_allOutputs_some`, `sidImpl_none_of_ne`, `expect_simulate_sidImpl_bb1RealAt`, `expect_sample_bb1RealAt`.
- `Coupling` (sub-agent A): `exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq`, `pair_pow_val_eq`, `stepM_call`.
- `Random`: `bb1SimLazy_random_call`.
- `Chain`: `prob_sidGame_coins`.

## The new declarations (namespace `TCSlib.Cryptography.AdvancedEncryption.IdentityBased`)

| full name (`BB1Sim.` = `…IdentityBased.BB1Sim.`) | home | kind | readers |
|---|---|---|---|
| `IBEScheme.sidImpl_zero_onSpec`, `_two_onSpec`, `_one_onQuery`, `_two_onQuery`, `_keyGen_ne_onSpec`, `_challenge_fresh_onSpec` | `Defs` | theorem (reader) | — |
| `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT` | `BonehBoyen` | theorem (reader) | — |
| `BB1Sim.sidSpec_dom_zero/_one/_two`, `sidSpec_rng_zero/_one/_two`, `zeroBits_eq_cast` | `Lazy` | theorem | — |
| `BB1Sim.bb1SimLazyChal` | `Lazy` | def | `bb1SimLazyChal_fresh`, `bb1SimLazyChal_of_not` |
| `BB1Sim.bb1SimLazy` | `Lazy` | def | `bb1SimLazy_eq`, `_zero`, `_one`, `_two_fresh`, `_two_of_not` |
| `BB1Sim.bb1SimImpl_zero_coins`, `_one_coins`, `_two_of_not`, `_two_fresh_allOutputs`, `_allOutputs_of_ne_two`, `expect_simulate_bb1SimLazy` | `Lazy` | theorem | — |
| `BB1Sim.RealReads` | `Real` | structure (Prop) | its fields `encPP`, `msgSpace`, `keyGen`, `enc` |
| `BB1Sim.setup_out` | `Real` | theorem | — |
| `BB1Sim.BB1RealState` | `Real` | abbrev | (notation) |
| `BB1Sim.bb1RealAt` | `Real` | def | `bb1RealAt_none`, `bb1RealAt_some` |
| `BB1Sim.bb1RealLazy` | `Real` | def | `bb1RealLazy_zero_none`, `_none_of_ne`, `_some` |
| `BB1Sim.sidImpl_allOutputs_some`, `sidImpl_none_of_ne`, `expect_simulate_sidImpl_bb1RealAt`, `expect_sample_bb1RealAt`, `expect_sample_sidImpl` | `Real` | theorem | — |
| `BB1Sim.exists_equiv_mul_pow`, `natCast_bitsToNat_injective`, `key_eq`, `F_target_eq`, `pair_pow_val_eq` | `Coupling` | theorem | — |
| `BB1Sim.RelM` | `Coupling` | def | `relM_iff` |
| `BB1Sim.stepM_call`, `expect_simulate_bb1RealLazy` | `Coupling` | theorem | — |
| `BB1Sim.bb1SimLazy_random_call`, `expect_bb1SimImpl_random` | `Random` | theorem | — |
| `BB1Sim.prob_sidGame_coins` | `Chain` | theorem | — |

**Expected later additions, to be listed in the final:**
- step M's call-by-call rows (`stepM_init_none`, …, `stepM_challenge_fresh`, named in `Coupling`'s module docstring), written by sub-agent A;
- a generalization of `bb1SimImpl_two_of_not`. Its right-hand side becomes `bb1SimImpl false … 1 1 2 x s`, so the call reads neither its coins nor the challenge bit; T3's comparison uses this. It is more general, and will be disclosed.

`RealReads` and `setup_out` are the probe's statements, in namespace `BB1Sim`.

## Outline: T2's and T3's chains mapped to the helper lemmas

Write:
- `S := bb1Scheme G ℓ`, `c(ρ) := A.toComp (S.sidCodec κ) κ q ρ`;
- `P(impl) := 𝔼[res ↦ Pr[res.1 0 = true]] (simulate impl c(ρ) (none, none))`;
- for generator coins `r`: `d := desc(κ, r)`, `B := G.group κ d`, `p := B.order`.

### T2 `bb1_sim_real` (the body is in `BonehBoyenSecurity.lean`)

0. **Read `Setup`.** `obtain ⟨o, hset, hR⟩ := BB1Sim.setup_out G ℓ κ`.
   - `rw [sidGame_eq, hset, bb1SimGame_eq, prob_bind]` writes both acceptances as `𝔼_r F₀ r` and `𝔼_r F₁ r`.
   - `ProbComp.abs_expect_sub_le_expect` with the pointwise bound `|F₀ r − F₁ r| ≤ 1[p < 2^ℓ]`:
     - on bad coins, both terms are probabilities (`prob_nonneg`, `prob_le_one`);
     - on good coins, `F₀ r = F₁ r` is **`BB1Sim.prob_sidGame_coins`**.
   - Then `prob_eq_expect` and `Bridge.prob_sample_eq_uprob` give `uprob`.
1. **`BB1Sim.prob_sidGame_coins`** (`Chain`), for each good `r`, after `prob_bind`. Fix `g`, then `α = a`:
   1. Move `h` past `g₂` and `ρ` (`expect_sample_comm`).
   2. **R1 + E-h**, by **`BB1Sim.expect_sample_sidImpl`** (`Real`), with `o' := fun h => o r g α h g₂`:
      - **R1** = `expect_simulate_sidImpl_bb1RealAt`, an instance of **`ProbComp.expect_simulate_rel`**:
        - `impl₀ := S.sidImpl b κ (o' h).1 (o' h).2` on `S.SidState κ`;
        - `impl₁ := bb1RealAt … o' h` on `BB1RealState`;
        - `R s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.
      - **E-h** = `expect_sample_bb1RealAt`, an instance of **`Games.expect_simulate_eager`**:
        - `O := bb1RealLazy … o'`;
        - `OE h := bb1RealAt … o' h`;
        - `used u := u.1.isSome`.
   3. `g₂ = g^{b'}`: `expect_sample_equiv` along `Equiv.ofBijective _ (pow_val_bijective_of_ne_one g.2)`. Then `hR` gives `RealReads … g α (g^{b'}) h (o' h)`.
   4. **Step M**: **`BB1Sim.expect_simulate_bb1RealLazy`** (`Coupling`), an instance of **`ProbComp.expect_simulate_rel`**:
      - `impl₀ := bb1RealLazy … o'`;
      - `impl₁ := bb1SimLazy b κ d g (g^α) (g^{b'}) zt_c`, with `zt_c c := (g^c, e(g, g)^{α b' c})` and `U = Z_p`;
      - `R := RelM … g (g^α)`;
      - the per-call hypothesis is `stepM_call`, from the rows and the algebra lemmas;
      - good coins enter through `natCast_bitsToNat_injective` (`CharP.natCast_injOn_Iio`, BS-F01).
   5. **E-c**: **`BB1Sim.expect_simulate_bb1SimLazy`** (`Lazy`), an instance of **`Games.expect_simulate_eager`**:
      - `O := bb1SimLazy … zt_c`;
      - `OE c := bb1SimImpl b κ d g (g^α) (g^{b'}) (g^c) (e(g, g)^{α b' c})`;
      - `used v := v.2.isSome`.
   6. On the simulation side:
      - `if true then … else t` is the real `T`, and the unused `T` drops out (`expect_const`);
      - `(a, b', c)` splits into three draws (`Bridge.expect_sample_pair`, `expect_bind`, `expect_pure`);
      - `c` moves past `ρ` (`expect_sample_comm`).

### T3 `bb1_sim_random` (the body is in `BonehBoyenSecurity.lean`)

1. `rw [advantage_eq, abs_eq_zero, sub_eq_zero, accept_eq, bb1SimGame_eq]`, then `simp only [prob_bind, if_false]` (`T` is the sampled `t`). Then fix `r`, `g`, `abc`, exchange `t` with `ρ` (`expect_sample_comm`), and fix `ρ`.
2. **`BB1Sim.expect_bb1SimImpl_random`** (`Random`):
   1. **E-T**: **`BB1Sim.expect_simulate_bb1SimLazy`** on each side, with `zt T := (Z, T)` and `U = G_T`:
      - `O := bb1SimLazy b' … (fun T => (Z, T))`;
      - `OE T := bb1SimImpl b' … Z T`;
      - `used v := v.2.isSome`.
   2. **`ProbComp.expect_simulate_congr`** compares `bb1SimLazy false` and `bb1SimLazy true`, with the per-call `bb1SimLazy_random_call`. At the first valid `Challenge` it uses **`ProbComp.expect_sample_rel`** with `R := Eq` along `T ↦ decodeT(M₁)⁻¹ · decodeT(M₀) · T` (the probe's P-3); every other call is the same for both bits.

## Statement changes

None. The four targets' headers and statement prose, `bb1_sidSecure` and `prob_simulate_rel` are untouched. The frozen-header check comes at the final.

## Scope requests

None.

## Questions for Seyoon

None at this checkpoint.

## Evidence

`evidence/SHA256SUMS` lists every evidence file. The top-level `SHA256SUMS` lists every delivered file.
