# gsw-6b-u12 · final

**Head: `afdaa9e2f29604052537652bf01165e61c52fb32`** (`fill/gsw-6b-u12`, local only).
**Base:** B6 `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc982fd8f79aba755796bb13188922c4655d`.

**All three targets are proved:** G1 `Encrypts.select`, G2 `encrypts_homEvalPBP`, G3
`encrypts_homEvalFormula`. There is no `sorry` in `Branching.lean`. No statement changed, no hypothesis was
added, and no scope request is open. Every check C1–C13 and the unit checks were run again at this head
for the final and pass (§5).

Checkpoint 1 (the same head, `afdaa9e2`, with all three targets already proved) was delivered as
exchange commit `f190df177`. The final adds nothing to the source. It re-runs every check under the tag
`final` and keeps the checkpoint's evidence beside it (`*-cp1*`).

One input question: **`rulings.md` does not exist** in `briefs/lattice-gsw/phase6/issued-6b-fills-r1/` at
the records pin `bbc930b3`, nor at the records tip at delivery (`978fd46c`). README *Blocking* 2 says U12
depends on no question, so I worked to `COMMON.md`, `U12/brief.md` and `dup-sweep.md` as issued (U12-W1).

## 1. Inputs, base, records tip, commits

- **Inputs** (`evidence/base/inputs-check.log`). Read at `bbc930b3853adb29ba96324568e984d521abd257`:
  - all 17 COMMON §1 files equal their SHA-256 values, so there is no E-INPUT;
  - the folder's `SHA256SUMS` gives 43/43 OK;
  - the folder `rulings.md` is ABSENT (above).
  - The addendum was read (Part 1; the *Lean parallelism* text of its 6b adaptation).
- **Base** (`evidence/logs/base-check.log`). `git rev-parse HEAD HEAD^{tree}` gives `bff0567b…`, `845bdc98…`, as expected.
  - The clone is separate: `git init`, then `git fetch --depth=1 file:///workspace/tcslib <B6>`, then the local branch `fill/gsw-6b-u12`.
  - `/workspace/tcslib` is this host's shallow mirror of the GitHub repository.
- **Records tip at delivery:** `978fd46c18662882b5831b6b1c6049975d52086d`.
  - `git merge-tree --write-tree afdaa9e2 978fd46c` is clean: rc 0, tree `b84570950ff49435ea213ef47eecd8bac12cc39e` (`evidence/git-merge-tree-final.txt`; the same at checkpoint 1).
  - I stayed on the base.

| # | Commit | File |
|---|---|---|
| 1 | `f0a51d1ed18253596aba2bf2f8450c8f93b186bf` | `GSW/Branching.lean`: G1–G3, one private glue lemma, three refreshed sketches, the module sentence |
| 2 | `afdaa9e2f29604052537652bf01165e61c52fb32` | `GSW/Branching.lean`: the glue's docstring formula now shows its `ℤ` cast |

Both commits are unsigned (`git -c commit.gpgsign=false`; `gpgsig` count 0), and each touches only the owned file.

## 2. Preflight, cache, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4. There is no cgroup memory limit, so the headroom is `MemAvailable` = 15.31 GiB (floor 4): pass.
  - **Disk.** The first reading was 10.36 GiB free, below the 12 GiB floor. I deleted two of my own finished, delivered worktrees of an earlier job on this host: `/workspace/scc` (its branch `fill/sc-compose` is kept as a ref) and `/workspace/scbase` (a detached base checkout). That freed 3.7 GB.
  - Nothing was copied, moved or deduplicated. The re-run gave **13.85 GiB free on ext4: pass**.
  - Before the cache step the re-check gave 10.29 GiB (floor 8): pass.
- **Packages.** `.lake/packages` is a symlink to this host's populated tree at exactly the manifest's pins (the addendum's alternative): 11 match, 0 mismatch, 4 absent (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`). Nothing in the order imports the absent ones (`evidence/logs/packages-check.log`).
- **Cache.**
  - The roots computed from `order.txt` are the 102 of `roots.txt` (`mathlib-roots.txt`).
  - Before the fetch, the store held 2,402 files (120,571,432 B), left by my earlier jobs on this host (`cache-store.log`).
  - The narrowed `lake exe cache get` (102 roots) exited 0: "No files to download", 2,339 decompressed (`cache-get.log`).
  - There are 0 empty oleans, and the cache probe (`import Mathlib.Algebra.BigOperators.Field`) compiles (`cache-probe.log`).
- **Pool** (`evidence/logs/pool.log`, tool `tools/pool.py`):
  - **3** Lean processes, in dependency order, each module through `scripts/lean_check_tree.sh`.
  - 3 = `min(nproc 4, MemAvailable 15.2 GiB / 4 GB)`, which is also the local-host cap. No other job's Lean process ran on the host. Never resized, no shortage.
  - Peak RSS per module: 2,952,176 KiB (`BonehBoyenMachine/Handler`, bootstrap). Peak host memory in use while the pool ran: 1.96 GB above idle.
- **Who did what.** One worker, no sub-agents: the lead wrote everything.

## 3. The owned file

| File | Base | Head | Fill | Estimate | Max width |
|---|---|---|---|---|---|
| `GSW/Branching.lean` | 179 | 268 | +89 | 150–250 | 97 |

The fill is below the estimate: the host lemmas (C7, C8) and Barrington's C14–C16 do all the induction.

## 4. Per target

### G1 `Encrypts.select`

**Route.**
- `select_eq` gives `(G − C) ⊡ U + C ⊡ V`.
- `Encrypts.sub` with `encrypts_gadget` gives `G − C` encrypting `1 − b` with noise `0 + β`.
- Case on `hb` (`rcases … rfl | rfl`).
  - The product whose left operand encrypts the bit `1` is **`Encrypts.mul_bit`** (with `b := true`, the message read by `simpa`), noise `N·β + βV`.
  - The product whose left operand encrypts `0` is `Encrypts.mul`, noise `N·β + |0|·βV`.
- `Encrypts.add`, then `Encrypts.mono` with `simp; omega` on the two concrete numerals.

No general `|1 − b| + |b| = 1` lemma is stated.

**Why not `mul_bit` twice.** `Encrypts.mul_bit` on the `0`-bit product would charge an extra `βV`, giving `2·βV + 2·(N·β)`, which is over the frozen bound. That product needs `Encrypts.mul`'s `|0|·βV = 0` term (§7).

### G2 `encrypts_homEvalPBP`

**Route.** `BranchingProgram.evalWith_rel` (C7) relates the homomorphic run (`select P`, `cts`, `Pi.single s₀ G`) to the Boolean run (`fun b u v => if b then v else u`, `x`, `Pi.single s₀ 1`). The relation is `R τ U U' := ∀ i, Encrypts P t (U' i) (τ·(2·(N·β))) (U i)`.
- **Step 0:** `encrypts_gadget` and `encrypts_zero` through `Pi.single_eq_same` and `Pi.single_eq_of_ne`.
- **Step `τ`:** the instruction `B.instrs[τ]` is a permutation (`isPermutation_iff`, then `Instr.isPermutation_iff`), so both steps take the pull form (`Instr.stepWith_of_isPermutation`, C6, rewritten in both runs). Then the private glue `encrypts_select_ite` gives noise `τ·X + X`, and `Encrypts.mono` with `ring` gives `(τ+1)·X`.
- **End:** `evalWith_single` (C8) gives the Boolean result `Pi.single (B.yield x s₀) 1`, and coordinate `i` is `(decide (B.yield x s₀ = i)).toNat`, by cases with `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `decide_eq_true` and `decide_eq_false`.
- The `homEvalPBP_eq` reader is used.

The relation carries no `0`/`1` side condition: the glue holds for any natural messages.

### G3 `encrypts_homEvalFormula`

**Route.**
- `homEvalFormula_eq`, then G2 for `barrington c sigma1` (`isPermutation_barrington`, C15) at `s₀ = 0`, `i = sigma1 0`.
- `sigma1 0 ≠ 0` by the reader `sigma1_eq` and kernel `decide` on Mathlib's `List.formPerm` over `Fin 5`.
- The message comes from `barrington_yield_zero hc isFiveCycle_sigma1 x` (C16, C9) and cases on `c.eval x` (`if_pos`/`if_neg`, `decide_eq_true`/`decide_eq_false`).
- The noise comes from `barrington_length_le hc sigma1` (C14) and `Encrypts.mono`.

**Why not `isFiveCycle_iff`.** The library's fact "a five-cycle moves every point" is `private` (`Barrington.lean:384`, `IsFiveCycle.apply_ne`), so it cannot be used, and re-deriving it would be a cross-file copy. The brief's alternative, `decide` on `Fin 5`, goes through the published reader `sigma1_eq`, so `sigma1` is not unfolded. The seals confirm this (§5).

### Helper (one, private)

`encrypts_select_ite` (Glue): if `C` encrypts `b.toNat` (`b : Bool`) with noise `β`, and `U`, `V` encrypt the naturals `u`, `v` with noise `βV`, then
`Encrypts P t ((if b then v else u : ℕ) : ℤ) (βV + 2 * (P.columns * β)) (select P C U V)`.

Its proof is G1 at `b.toNat`, then `cases b <;> simpa`. It is the Boolean-selector form that the host's Boolean run needs.

### Readers used

`select_eq`, `homEvalPBP_eq`, `homEvalFormula_eq` (own).

`Noise.lean`: `encrypts_gadget`, `encrypts_zero`, `Encrypts.mono`, `.add`, `.sub`, `.mul`, `.mul_bit`.

`BranchingPrograms`: `evalWith_rel`, `evalWith_single`, `Instr.stepWith_of_isPermutation`, `isPermutation_iff`, `Instr.isPermutation_iff`, `length_eq` (as `evalWith_rel`'s statement writes the index bound), `isPermutation_barrington`, `barrington_yield_zero`, `barrington_length_le`, `isFiveCycle_sigma1`, `sigma1_eq`.

Mathlib and core: `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `decide_eq_true`, `decide_eq_false`, `if_pos`, `if_neg`, `Nat.cast_one`, `Nat.cast_zero`, `zero_mul`.

The census with `path:line` is `evidence/rule10/reader-census.txt`: MISSING 0.

### Imports and sketches

**Imports:** none added.

**Sketches refreshed (statement prose untouched; the frozen check passes):**
- **G1.** Old: "`Encrypts.mul` gives `(G − C) ⊡ U` with noise `N·β + |1 − b|·βV` and `C ⊡ V` with noise `N·β + |b|·βV`, the two products that `select_eq` exposes. `Encrypts.add` sums the two; since `b ∈ {0, 1}`, `|1 − b| + |b| = 1`, so the noise is at most `βV + 2·(N·β)` by `Encrypts.mono`, and the message is `(1 − b)·u + b·v`."
  New: "`select_eq` exposes the two products `(G − C) ⊡ U` and `C ⊡ V`. Case on `b ∈ {0, 1}`. The product whose left operand encrypts the bit `1` is `Encrypts.mul_bit`, with noise `N·β + βV`; the other left operand encrypts `0`, and `Encrypts.mul` gives noise `N·β + |0|·βV = N·β`. `Encrypts.add` sums the two, the message is `(1 − b)·u + b·v`, and the noise `2·(N·β) + βV` is at most `βV + 2·(N·β)` (`Encrypts.mono`)."
- **G2.** Old: "…; the messages agree because the Boolean coordinates are `0`/`1` and the selector picks the branch of `x var`. At `τ = B.length` read `evalWith_single` and `Pi.single_apply`."
  New: "…; the messages agree because `(1 − b)·u + b·v` at `b = (x var).toNat` is the Boolean branch `if x var then v else u` (the private glue `encrypts_select_ite`). At `τ = B.length` read `evalWith_single` and `Pi.single_eq_same`, `Pi.single_eq_of_ne`."
- **G3.** Old: "`sigma1 0 ≠ 0` (a five-cycle has no fixed point: `isFiveCycle_iff`, or by `decide` on `Fin 5`)".
  New: "`sigma1 0 ≠ 0` (`sigma1_eq` and kernel `decide` on `Fin 5`)".
- **Module docstring.** "All three are statement-phase targets (admitted); …" became "All three are proved here; …".

## 5. Checks (C1–C13 and the unit checks; full runner `tools/lead/checks.sh`, log `evidence/checks-final.log`; checkpoint 1's run: `checks-cp1.log`)

- **C1 Bootstrap and sweep.**
  - Bootstrap of `order.txt` at the base: **224/224 rc 0, 0 errors** in both forms (`evidence/build/bootstrap.tsv`, logs `bootstrap/`).
  - The sorry census equals `base-sorries.txt`: **42 in 16**, name by name (`sorry-census-base.txt`).
  - All 224 sources equal `SOURCE-SHA256SUMS` (`source-binding-base.txt`: 0 mismatches).
  - Head sweep of the 10 `UNIT-DOWN` modules: Branching, Bootstrap, Circular, Leveled, LeveledSecurity, PolyRatio, Asymptotic and the three facades. Branching is the only changed module, so this is "changed + downstream". All **10/10 rc 0, 0 errors**, each source bound to `git show HEAD` (`evidence/build/summary-final.txt`: `RESULT modules=10 bad=0`).
  - The root `TCSlib` is not built.
- **C2 Admissions.** At the head: **39 declarations in 15 modules** = `base-sorries.txt` minus G1–G3, with the diff exactly the Branching row (`admissions-final-vs-base.txt`). No `sorry` token in the owned file. Nothing remains open.
- **C3 Statements.**
  - decls2 gives **0 ADDED, 0 CHANGED, 0 REMOVED** (`evidence/stmt/decls2-final-summary.txt`).
  - The StmtDump of the three targets (full names) is identical at base and head (`StmtDump-base.stripped`, `StmtDump-head-final.stripped`, `StmtDump-diff-final.txt`).
- **C4 Frozen check** (`tools/lead/frozen_owned.py`, the 6a fill's tool with one added control). **PASS, 0 differences** against `allow.tsv`, which licenses only the module sentence.
  - The seven controls each FAIL as stated: header 1, prose spill 1, definition body 1, reader 1, unpermitted import 1, deleted target 2, unlisted new public declaration 1.
  - The unchanged file passes (`frozen-base-vs-base.txt`).
  - `git diff --stat` lists only `Branching.lean` (`git-diff-stat-final.txt`).
- **C5 Axioms** (`evidence/axioms/AxiomProbe-final.log`). All 13 stored constants of the module (auxiliaries and the private glue included) use only `propext`, `Classical.choice` and `Quot.sound`.
  - **No `sorryAx`**: `SORRY-REACHING 0`, so the dependency trace is empty, as the brief requires.
- **C6 Rule 10** (`evidence/rule10/`).
  - Whole-file seals strict-A, strict-B, coe-A and coe-B, `-DmaxErrors=0`, over the full import closure (census 945 constants, 200 requests), at the head (`final/`) and at the base (`base/`). **All 8 probes rc 0, 0 errors, no failing declaration**, each with its install and verify records.
  - The request sets were rebuilt at the base from its own oleans.
  - **Notation exemptions.** `PolyExpr.eval` and the `FinDist` coercion are not in this closure, so A = B and strict = coe here.
  - **Liveness pair** (`live-final/`, source `live-src/`), appended to the owner's own probe:

    | Variant | Negative (`BranchingProgram.evalWith` by `rfl`) | Positive (`evalWith_eq`) |
    |---|---|---|
    | unsealed (pretest) | 0 errors | 0 errors |
    | strict-A, strict-B, coe-A, coe-B | exactly 1 error each | 0 errors |

  - There is no new public definition, so no further pair is needed.
  - Explicit-unfold scan: 19 identifiers, **0 foreign definitions** (`unfold-final/explicit-unfold-scan.txt`). The reader census has no MISSING entry.
- **C7 Lint.**
  - `style_lint` on the owned file: 0 findings.
  - `campaign_style_lint TCSlib/Cryptography --check8b`: **92 FAIL / 103 WARN over 540 files** at both base and head, matching the maintainer's B6 figures. The line sets are identical: no new or gone FAIL or WARN (`campaign-diff-final.txt`).
- **C8 Sizes:** §3 (`evidence/sizes/sizes-final.txt`). No line over 100, no file over 1,000.
- **C9 Hygiene** (`evidence/docs/hygiene-final.txt`). The one helper has a formula and "Glue.". G1 (21 lines), G2 (49) and G3 (26) have sketches, and G2's proof has step comments at its `have`s. **flagged = 0**.
- **C10 Clashes** (`evidence/clash/clash-final.txt`). One new name, private: `encrypts_select_ite`.
  - It has 0 hits at the base, on `iO/phase-a-base` (`5ed465f6…`), on `cleanup/stage2-s2a` (`dff281b5…`) and at the records tip.
  - Being private, it cannot change any resolution in a `UNIT-DOWN` module.
- **C11 Reuse and overlap:** §6.
- **C12 Probe U12-P1** (`evidence/probes/U12-P1.log`, source `probe-sources/probes/U12P1.lean`). `#eval` of `select` on toy parameters `n = 1`, `q = 8`, `ℓ = 3`, with noise-free `b·G`, `u·G`, `v·G`, against `((1 − b)·u + b·v)·G` entrywise: **true for all 10 cases** (the four bit pairs with `u, v ∈ {0,1}`, plus `(b, 5, 3)` for `b = 0, 1`). Evidence only; no `native_decide`.
- **C13 Reproduction** (`evidence/reproduce-final.log`). In a scratch clone (sparse to the owned file), reset to the base, `git am` of `patches/` with `COMMITS.tsv`'s committer data reproduces both hashes, and `src/` equals the head's file byte for byte.

## 6. Overlap and reuse

**Searches** (`evidence/overlap/searches.txt`; 10 `rg` searches over TCSlib and Mathlib at the head, with hit counts), and `exact?` probes on the glue's and the inline facts' statements (`evidence/overlap/DupProbe.log`). Results:
- **P1 glue:** no lemma.
- **P2/P3** (`Pi.single a 1 i` as `(decide (a = i)).toNat`): no lemma, in ℤ or ℕ.
- **P4** (`sigma1 0 ≠ 0`): `exact?` only computes it (`Ne.symm (not_eq_of_beq_eq_false rfl)`), which would unfold `sigma1`. No published lemma.

**`dup-sweep.md` §U12 must-reuse items:**

| Item | Where used |
|---|---|
| `Encrypts.mul` | G1, the `0`-message product |
| **`Encrypts.mul_bit`** | G1, the `1`-bit product |
| `Encrypts.add` | G1 |
| `Encrypts.sub` | G1, `G − C` |
| `Encrypts.mono` | G1, G2 step, G3 |
| `encrypts_gadget` | G1, G2 step 0 |
| `encrypts_zero` | G2 step 0 |
| `mul_eq` | not needed: `select_eq` exposes `mul` and the closure lemmas take it as is |
| `encrypts_iff` | not needed: no error vector is opened |
| `select_eq`, `homEvalPBP_eq`, `homEvalFormula_eq` | G1, G2, G3 |
| `evalWith_rel` | G2 |
| `evalWith_single` | G2 |
| `Instr.stepWith_of_isPermutation` | G2 |
| `isPermutation_iff` (`Defs.lean:323`) | G2. `:450` is the family version and is not needed |
| `Instr.isPermutation_iff` | G2 |
| `isPermutation_barrington` | G3 |
| `barrington_yield_zero` | G3 |
| `barrington_length_le` | G3 |
| `isFiveCycle_sigma1` | G3 |
| `isFiveCycle_iff` | not used: the brief's `decide` alternative was taken (§4 G3) |

**The *Do not* list is respected:**
- the host induction is not re-proved;
- `evalWith`, `barrington`, `stepWith`, `yield` and `Encrypts` are not unfolded (unfold scan 0; seals clean);
- no general `|1 − b| + |b| = 1` lemma.

**Near relatives:**

| Relative | Relation |
|---|---|
| `Noise.lean:274` `Encrypts.nand` | bit-gate analogue of G1, not a selector |
| `Noise.lean:259` `Encrypts.mul_le` | bit-gate analogue of G1, not a selector |
| `Noise.lean:296` `encrypts_chain` | the additive-chain analogue of G2 |
| `Eval.lean:186` `stepWith_single` (private) | the Boolean one-step fact, used through C8 |
| `Barrington.lean:384` `IsFiveCycle.apply_ne` (private) | the general five-cycle fact behind `sigma1 0 ≠ 0`. Not copied: `sigma1_eq` + `decide` |

None of these is restated.

**Specialization disclosed:** `encrypts_select_ite` is G1 specialized to `b = c.toNat`, natural messages and the Boolean branch form, private glue in the same file. G1 is used, not re-proved. The two-line `Pi.single`/`decide` case split inside G2 states no general fact: no lemma exists for it (P2/P3).

## 7. Promotion requests, scope requests

- **Promotion request (optional):** a public `IsFiveCycle.apply_ne` in `Barrington.lean` (now private). It would let consumers read `σ 0 ≠ 0` for any five-cycle without computing on `sigma1`.
- **Scope requests:** none.

## 8. Questions for Seyoon

- **U12-W1 (no `rulings.md` at the pin).** The dispatch names `issued-6b-fills-r1/rulings.md`. It is absent at `bbc930b3` and at the tip `978fd46c`.
  - (A, recommended) Confirm "no rulings for this folder apply to U12" (README *Blocking* 2: U12 depends on no question).
  - (B) Point me to the rulings file. I will re-check this delivery against it.
- **U12-W2 (G1's route).** `dup-sweep.md` §U12 suggests `Encrypts.mul_bit` "for the two products". That cannot reach the frozen bound: `mul_bit` charges `βV` on the `0`-message product too.
  - (A, recommended) Accept `mul_bit` for the `1`-bit product and `Encrypts.mul` for the `0`-message product, as delivered (the brief's "or `Encrypts.mul` with `Encrypts.mono`").
  - (B) Amend the sweep's wording for later units.

## 9. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS`. Their paths equal the delivered files.

- `base/`: the inputs check.
- `logs/`: preflight, base check, packages, cache, pool, order and roots.
- `build/`: the bootstrap with its census and source binding, the sweep, the summary and the admissions.
- `stmt/`: decls2 and StmtDump.
- `headers/`: the frozen check, its allow list and targets.
- `axioms/`.
- `rule10/`: seals at the base and the head, liveness pair, unfold scan, reader census.
- `lint/`, `sizes/`, `docs/`, `clash/`, `overlap/`, `probes/`.
- `git-diff-stat-{cp1,final}.txt`, `git-merge-tree-{cp1,final}.txt`, `reproduce-{cp1,final}.log`, `checks-{cp1,final}.log`.
- `tools/`: the pool, census, StmtDump, check runner, seals, frozen check, unfold scan, lint diff, sizes and hygiene, delivery, and the records copy of `decls2.py`.
- `probe-sources/`: the Lean sources of every probe, cache probe included. `rule10/probe-sources/` holds the seal probes.
