# Fill report: ch34-fill-deepen (`Complexity.savitch` by iterative deepening)

**Outcome: complete.** `Complexity.savitch`, `Complexity.savitch_of_logSpace_le` and
`Complexity.LogProg.SavitchARM.deepen_contract` are proved, each on
`[propext, Classical.choice, Quot.sound]`. Proved modulo: nothing. No new admission.

- **Brief:** `campaign/fills/ch34/briefs/ch34-fill-deepen.md`, SHA-256
  `815ccc2e86f94824dad19ecab87d8d0f9cbaa8c7b426a6faa03fa3f4237f325c` (verified, attached copy and
  repository copy at records commit `a89e8d70` are identical).
- **Addendum:** `campaign/standards/fill-environment-addendum.md` v2.6, SHA-256
  `9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28` (verified, both copies).
- **Base:** `fd97df61f74851db82a0b68e1913a14ca5e77eac`. Branch `fill/ch34-deepen` was created at
  exactly that commit (`git rev-parse HEAD` printed it). The ancestor check
  (`git merge-base --is-ancestor fd97df61… HEAD` on `complexity/arora-barak-ch3-4`, tip `d7e0a6d3`)
  succeeded. No rebase, merge or cherry-pick.
- **Head:** `c7b179da4cdb9f091ad83167ffc0df1ec85d2d01` (commits below). The delivery has the patch series against the base and a
  bundle.

```
c7b179da Deepen: dp_block's proof sketch
362a6926 Deepen: one lemma (dp_block) for a block's preparation and run, shared by both steps
17011e44 Deepen: cite register_update_le (InputAccess) for the register bound; drop dp_bd
fb86be7b Deepen: cite Codec.halvCount_loop for the halving loop (no own loop); drop unused steps
82349b7d Deepen: one induction for the halving count's two bounds (removes a within-file screen pair)
6c8e70fa Deepen: the deepening machine and deepen_contract; savitch_of_logSpace_le and savitch proved
1c31f6e8 Deepen: the overlay (three imports and the pins) and its import lines
```

## 1. Environment (addendum Part 1)

### Preflight (`evidence/logs/preflight.log`), before any cache or Lean work

| item | value |
|---|---|
| `nproc` | 4 |
| memory (cgroup v1, own cgroup `…/claude-code-bash`) | `memory.limit_in_bytes` 14,337,302,528; `memory.usage_in_bytes` 818,802,688; `total_cache` 764,149,760; `total_shmem` 0; `failcnt` 0; `oom_kill 0` |
| headroom (v1 formula: limit − (usage − total_cache + total_shmem)) | 14,337,302,528 − (818,802,688 − 764,149,760 + 0) = 14,282,420,224 B = **13.30 GiB** (floor 4 GiB) |
| clone `/home/user/tcslib`: `df -B1`, `df -T` | 31,476,809,728 B available = **29.32 GiB** (floor 12 GiB); ext4 (`/dev/vda`) |
| scratch directory (session scratchpad), `TMPDIR` | same ext4 filesystem; `TMPDIR` unset (`/tmp`, ext4). Nothing on tmpfs or `/dev/shm`. |

Both floors pass. The toolchain (elan, `leanprover/lean4:v4.25.0`) was installed after the
preflight. Its 12 GiB floor covered that, so no re-check was needed (29 GiB remained).

### Part 2 (unreadable `/proc/<pid>/exe`)

Not needed. The unmodified Lean started normally (`lean --version`:
`Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5…, Release)`,
`evidence/logs/toolchain.log`). No shim was compiled or preloaded.

### The cache

- **Archive store, logged before the first fetch** (`evidence/logs/cache-store.log`):
  `/root/.cache/mathlib` did not exist (0 files, 0 bytes). Every archive below was downloaded by
  this session.
- **Roots:** 63 (`evidence/logs/mathlib-roots.txt`), computed by the addendum's command from the
  order list after the first edit. They equal the pre-ship log's list, line for line.
- **Fetch:** `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat mathlib-roots.txt)`
  (`evidence/logs/cache-get.log`). The cache tool compiled itself (`[20/20] Built cache:exe`) and
  installed `leantar 0.1.16`. That is the tool's own work, outside the one-Lean rule (v2.6) and not
  a deviation. Result: "Attempting to download 1057 file(s)", 1057 downloaded, "Decompressing
  1057", "Completed successfully!", exit 0. 1057 − 1057 = 0 archives came from the store. No
  failed download, no retry. The unfiltered `lake exe cache get` and `lake build` were never run.
- **Item 3 checks:**
  - `find .lake/packages -name '*.olean' -size 0` printed nothing.
  - The probe `import Mathlib.Algebra.BigOperators.Field` (the first root) elaborated through
    `scripts/lean_check_tree.sh` (exit 0, 1.8 s; `evidence/logs/cache-probe.log`).
- **Manifest check** (`evidence/logs/manifest-check.log`): every present package matches the
  manifest's URL and revision (PFR, mathlib, Cli, LeanAPAP, plausible, LeanSearchClient,
  importGraph, proofwidgets, aesop, Qq, batteries).
  - ABSENT: `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`. No module of the order list
    imports them.
  - Last line: `manifest check: PASS; present all match; absent: «doc-gen4», UnicodeBasic,
    BibtexQuery, MD4Lean`.

### Bootstrap (`evidence/logs/bootstrap.log`)

- After the first edit (the overlay: `Deepen.lean` with its three imports and the pins, and the
  import lines in `Savitch.lean` and the facade), the **whole order list was built** (196
  modules, in order, one Lean process at a time), not only `Deepen`'s ancestors.
- 196/196 passed, total wall time 1,524 s.
  - Peak memory: `Codec/Machine` 2,944,012 KiB (120 s), `Build/Catalog` 2,937,404 KiB (98 s),
    `Build/CfgRecord` 2,935,424 KiB.
  - Longest module: `Machines/NARMProb`, 221 s.
  - Each module's start, end, wall time and maximum RSS is on its `TIMED` line.
- Its sorry warnings were exactly the base set's 26 entries in 10 modules plus the overlay's
  `deepen_contract` (`Deepen.lean:30`). There were no errors.
- **Timing tool:** this host has no `/usr/bin/time`. Each check ran under
  `evidence/runtime/timed.py`, which records start and end (UTC), wall time, exit status and the
  child process tree's maximum resident set (`getrusage(RUSAGE_CHILDREN)`, KiB), one process per
  module.

### Process disclosures (v2.6 Part 3 item 7: disclosed, the work continued)

1. **Draft written into the clone during the bootstrap.** At 00:36 UTC, while the bootstrap was
   at module 131 of 196, I wrote a first draft of `Deepen.lean` into the clone instead of the
   scratch directory. I noticed at once, moved the draft to the scratch directory, and restored
   the overlay before the bootstrap reached `Deepen` (module 141 began at 00:37:56). The bootstrap
   log shows module 141 elaborating the overlay (`Deepen.lean:30:8: warning: declaration uses
   'sorry'`, the overlay's `deepen_contract`), so the bootstrap is the overlay's. No Lean process
   read the draft during the bootstrap.
2. **The before-screen ran beside the bootstrap** (one text screen, `nice -n 10`, on a frozen
   `git archive` of the base). This is allowed by Part 3 item 5.
3. **The repository's `.claude/CLAUDE.md`** asks agents not to run `lean` and to use the VS Code
   infoview. The brief, binding and given by the user, requires `scripts/lean_check_tree.sh` for
   every check, and I followed the brief.
4. **Open PRs:** this session's GitHub API access is refused (GraphQL disabled, REST "not
   enabled"), so PR open/closed status could not be read. The semantic search therefore covered
   every `refs/pull/*/head` that is contained in neither the campaign branch nor `main`. That is
   16 heads (#76, #77, #185–#187, #191–#193, #195, #198, #199, #201–#205), a superset of the open
   PRs (§6).

## 2. Checkpoints

**All eight reached.** Checkpoints 1–7 landed together, in the first elaboration pass of the full
`Deepen.lean` (commit `6c8e70fa`, with `Savitch.lean`). Later commits only replaced own helpers
by published rows, which the semantic search and the screen asked for (§6, §7). Each checkpoint
zip `fill-ch34-deepen-cp<N>.zip` holds the state at the end of the session. They are identical
except for `CHECKPOINT.txt`, which names the checkpoint and its declarations.

| cp | content | declarations (`Deepen.lean` unless noted) |
|---|---|---|
| 1 | labels, table, deciders, oracle bridges, table equations, `PreS` | `DpLb`, `dpρ`, `dpρ_inj`, `dpρ_ne`, `dpCopyI`, `dpShlI`, `dpCbEx`, `dpCtEx`, `dpCt0`, `dpIn`, `dpkE`, `dpσE`, `dpσA`, `dpD`, `dpAs`, `dpOrc`, `dp_mem`, `dp_rel`, `dp_initO`, `dp_accO`, `dp_pre`, `dp_inc`, `dp_clr`; table equations are `rfl` at every use (`fun _ => rfl`) |
| 2 | setup: `n`, `ℓ`, `s := 1` | in `dp_run`: `inputLength_loop`, `dp_inc`, `Codec.halvCount_loop`, `dp_inc`; `dp_bits_logSpace` |
| 3 | `w`, `2 ^ w`, register reset and its `RegExt` | `dpSt`, `dpSt_ρ`, `dpSt_own`, `dpSt_upd_ρ`, `dpSt_upd_own`, `dpSt_bd`, `dp_copy`, `dp_shl`, `dp_cb_run`, `dp_cT_run`, `dp_prep`; the `RegExt` is built in `dp_fit` (`⟨hv, fun _ _ => rfl⟩`) |
| 4 | the two blocks' runs | `dp_fit` (one `AHalt.embed_guardLe` of `outerU_run`), `dp_bd_blk`, `dp_block` |
| 5 | the loop | `dp_edge`, `dp_acc`, `dp_body` (induction on `sp |x| + 1 - s`) |
| 6 | register bound and guard in the contract's form | `dpW`, the guard `GuardLe D x (2 ^ (dpW · dpW))` along `dp_body`/`dp_run`, converted in `deepen_contract` |
| 7 | `deepen_contract` | `deepen_contract` |
| 8 | `Savitch.lean` | `savitch_of_logSpace_le` (route probe's proof), `savitch`'s body `savitch_of_logSpace_le S hS.1`, its docstring, the module docstring's Status and Design, the facade's import line and module-list line |

## 3. The machine `D`

`D = dpD (codeK N + 1) : ARM 25 5 (DpLb (codeK N + 1))`, start label `scan`. The search block
is `A 0`: one fixed `E = 0`, whose setup labels are dead code, since `outerU_run` holds for every
`E`.

**Registers** (25):
- `0 … 17`: the block, through `ρ = dpρ`, `ρ r = r` (injective: `dpρ_inj`).
- `D`'s own registers, all off `ρ`'s range (`dpρ_ne`): `18 T` (`s + ℓ + 1`), `19 W` (the width
  `w`), `20 C` (shift counter), `21 N` (`|x|`, halved to `0` by the setup), `22 ℓ`, `23 s`,
  `24 Z` (the loops' scratch register, `0` between loops; also each block's `r₀`).
- Between loops the register file is `dpSt b o`: block part `b`, own part `o`.

**Deciders** (binding row): `As = dpAs N = ![inputLenLang, initLang N, acceptLang N, stepLang N,
edgeLang N]`. They are in `LOGSPACE` by `inputLenLang_mem`, `initLang_mem`, `acceptLang_mem`,
`stepLang_mem` and `edgeLang_mem`. The oracle is the indicator family (`dpOrc N`, the contract's
`fun j V => indicator (As j) V`).

**Blocks** (binding row): `A 0`'s table twice, through `Ins.embed`.

| block | labels `ι` | `σ` | exits `k` | `r₀` |
|---|---|---|---|---|
| edge | `eb : Lb 0 → DpLb c` | `dpσE = ![0, 1, 4, 3]` | `dpkE`: `true ↦ nxt`, `false ↦ cb true 0` | 24 |
| accept | `ab` | `dpσA = ![0, 1, 2, 3]` | `fin` (`fin b = ret b`) | 24 |

**Each block's fit** is `dp_fit`, which is `fit_edge_block`'s proof shape, generalized over `σ`,
the decider `j = σ 2`, its language `La = dpAs N j` and the run's bound `B ≥ 2 ^ (w · w)`:
- `rw [← setSt_toV, ← outerSt_toV]` on the entry `RegExt`;
- one `AHalt.embed_guardLe dpρ_inj hD (A_noVal 0) hBB he (outerU_run …) hR`;
- the oracle read through `rel_iff_orc`, `stepRel_iff_mem`, `initO_iff_orc`, `accO_iff_orc` and
  `indicator_eq_decide` (in `dp_rel`, `dp_initO`, `dp_accO`, `dp_mem`);
- the answer converted by `decide_eq_decide`.

It is instantiated twice, in `dp_block`: edge with `j = 4`, `La = edgeLang N`; accept with
`j = 2`, `La = acceptLang N`. The search is never re-proved, and `A`, `outerSt`, `InitO`, `AccO`
and `Rel` are never unfolded; the seal test confirms this (§5).

**Labels and loops** (`DpLb c`, `c = codeK N + 1`):

| phase | labels | run |
|---|---|---|
| `n := |x|` | `scan` (`call 0 .whole [21]`), `incN` | `inputLength_loop` |
| `ℓ := 1` | `lInc` | `dp_inc` |
| `ℓ += |bits N|`, `N := 0` | `hz` (`jz 21`), `hh` (`half 21`), `hi` (`inc 22`) | `Codec.halvCount_loop` |
| `s := 1` | `sOne` | `dp_inc` |
| prepare block `f` | `cb f i` (`clr i`, `i < 21`: registers `0 … 20`) | `dp_cb_run` |
| | `cS f j`, `cL f j` (`T += s`, `T += ℓ`), `tInc f` | `copy_run` (`dp_copy`) ×2, `dp_inc` |
| | `cT f i j` (`W += T`, `c` copies) | `dp_cT_run` (`copy_run` ×`c`) |
| | `bS f j` (block `rs += s`), `zW f` (`clr rw`), `bW f j` (block `rw += W`) | `dp_copy`, `dp_clr`, `dp_copy` |
| | `zK f`, `kOne f` (block `rK := 1`), `cC f j` (`C += W`), `sh f j` (`rK *= 2 ^ C`) | `dp_clr`, `dp_inc`, `dp_copy`, `shl_run` (`dp_shl`) |
| | `zU f`, `zV f`, `zM f` (clear `rU`, `rV`, `rM`) | `dp_clr` |
| next radius | `nxt` (`s += 1`, back to `cb false 0`) | `astep_inc` |
| answer | `fin b` | `AHalt.ret` |

The block-entry registers are written in the order `rs`, `rw`, `rK`, `rU`, `rV`, `rM`, each
right after clearing it, onto the all-clear block. The block part is then syntactically `setSt`'s
and `outerSt`'s `Function.update` chain. It is reached through `dpSt_upd_ρ` and
`Function.update_idem`, needs no register-distinctness facts, and does not depend on the register
names' values (which are sealed).

**Correctness** (`dp_body`, induction on `sp |x| + 1 - s`, from the body at any
`1 ≤ s ≤ sp |x| + 1`):
- `dp_edge`: the edge block exits with `b = false ↔ NoEdge N x s w`, read through
  `decide_eq_false_iff_not` and `noEdge_iff`; `NoEdge` is never unfolded.
- `b = false`: `dp_acc` runs the accept block, whose bit is `decide (x ∈ L)` by
  `mem_iff_reach_of_noEdge`.
- `b = true`: `s ≤ sp |x|` (otherwise `noEdge_of_lt` gives `b = false`), so `s + 1` stays in
  range and the induction hypothesis applies.
- At `s = sp |x| + 1` the bit is `false` (`noEdge_of_lt`).

**Departures from the recommended (non-binding) shape:**
- `w = (codeK N + 1)(s + ℓ + 1)`, not `codeK N · (s + ℓ + 1)`. `s ≤ w` (`outerU_run`'s
  hypothesis) needs a positive factor, and `codeK N ≥ 1` has no published lemma (its definition
  must not be unfolded). `mem_iff_reach_of_noEdge`'s `codeK N · (s + logSpace |x| + 1) ≤ w` still
  holds since `logSpace |x| ≤ ℓ`.
- `ℓ = 1 + |bits |x||`, through the published `Complexity.Codec.halvCount_loop`, instead of an own
  halving loop (§6).
- `N` is consumed by the halving (it is `0` afterwards), and `w`, `T`, `2 ^ w` are recomputed at
  every preparation. `ℓ` and `s` stay in `D`'s own registers throughout.

## 4. The constant `C` and the register bound

`C = 9 (codeK N + 1)² + 2`. Write `c = codeK N + 1`, `n = |x|`, `X = sp n + logSpace n + 1 ≥ 1`
(since `logSpace n ≥ 1`), `ℓ = 1 + |bits n|` and `W = dpW N sp x = c (sp n + 1 + ℓ + 1)`. Term by
term:

1. `ℓ ≤ logSpace n + 1` and `logSpace n ≤ ℓ` (`dp_bits_logSpace`, from `logSpace_le_size_succ`,
   `Nat.size_eq_bits_len`, `Nat.size_le`, `Nat.lt_pow_succ_log_self`).
2. Every radius reached has `s ≤ sp n + 1`, so every width `w = c (s + ℓ + 1) ≤ W`.
3. `W ≤ c (sp n + logSpace n + 3) ≤ 3 c X`.
4. Every register is at most `2 ^ (W · W)` along the whole run (the guard
   `GuardLe D x (2 ^ (W · W))`):
   - block registers: at most `2 ^ (w · w)`, by `embed_guardLe`'s second conjunct, and
     `2 ^ (w · w) ≤ 2 ^ (W · W)`;
   - own registers: at most `max(|x|, 2 ^ w)`, with `|x| < 2 ^ ℓ ≤ 2 ^ W`
     (`n < 2 ^ |bits n|`) and `w < 2 ^ w ≤ 2 ^ W ≤ 2 ^ (W · W)`.
5. A value `v ≤ 2 ^ (W · W)` has `v + 1 < 2 ^ (W · W + 2)`, so
   `|bits (v + 1)| ≤ W · W + 2` (`length_bits_le`).
6. `W · W + 2 ≤ 9 c² X² + 2 X² = C · X²` (using `X² ≥ 1`).

The guard is converted to the contract's form in `deepen_contract` by `AHalt.mono`.
`savitch_of_logSpace_le` (the route probe's proof, verbatim up to namespace prefixes) then uses
`C (c₀ + 2)²` for `arm_decides_SPACE`.

## 5. Edge cases

| case | what happens | covered by |
|---|---|---|
| `x = []` | `n = 0`; the halving loop exits at once, `ℓ = 1 + |bits 0| = 1` | `Codec.halvCount_loop` (its `n = 0` case); `dp_bits_logSpace 0` (`logSpace 0 = 1 ≤ ℓ`) |
| `N.k = 0` | no edge configuration exists, so `NoEdge` holds and the first edge block answers `false` | not special-cased: `dp_edge` (`b = false ↔ NoEdge`) with `noEdge_iff`; the accept branch of `dp_body` |
| `sp |x| = 0` | the loop stops at `s = 1` | `dp_body`'s `zero` case (`sp |x| + 1 - 1 = 0`), with `noEdge_of_lt` (`0 < 1`) |
| halving at `n = 0` | `jz` exits immediately, nothing added | `Codec.halvCount_loop`; `dp_run` (`e21`) |

## 6. Rule 10: no unfolding

### Citations: published equations and lemmas only

- **TCSlib, passed to `rw`:** `setSt_toV`, `outerSt_toV`, `rel_iff_orc`, `initO_iff_orc`,
  `accO_iff_orc`, `stepRel_iff_mem`, `indicator_eq_decide`, `noEdge_iff`, `logSpace_eq`,
  `astep_inc`, `astep_clr`.
- **TCSlib, applied:** `outerU_run`, `A_noVal`, `AHalt.embed_guardLe`, `preS_of_ins`,
  `RegExt.mk`, `copy_run`, `shl_run`, `inputLength_loop`, `Codec.halvCount_loop`,
  `register_update_le`, `indicator_inputLenLang`, `noEdge_of_lt`, `mem_iff_reach_of_noEdge`,
  `length_bits_le`, `logSpace_le_size_succ`, the `_mem` lemmas, `AReach.*`, `AHalt.*`,
  `reach_of_eq`.
- `Ins.embed`, `RegExt`, `PreS`, `astep`, `arun`, `AHalt` and `AReach` are never unfolded:
  `PreS` goes through `preS_of_ins`, steps through `astep_*`, `RegExt` through its constructor.
- `D` and the file's own definitions are unfolded only by `rfl` (table equations) and by
  `simp only [dpSt]`, `rw [dpOrc]` and `rw [hW, dpW]`.

### Seal test (`evidence/seal/`)

- **Generator:** `mkseal_deepen.py`. The sealed copy `DeepenSealed.lean` is the final
  `Deepen.lean` with, after `open Turing Codec`, the block fit's `attribute [-simp]` line and
  `attribute [local irreducible]` over 35 definitions:
  - the block fit's 22: `InitO`, `AccO`, `Rel`, `outerSt`, `setSt`, `St.toV`, `St.zero`, `rs`,
    `rw`, `rK`, `A`, `Reach`, `StepRel`, the four code languages, `MultiTapeTM.indicator`,
    `Ins.embed`, `AHalt`, `AReach`, `PreS`;
  - `NoEdge`;
  - its Loop section's `DecidesInSpace`, `codeK`, `logSpace`, `pairEncode`;
  - this fill's extension: `astep`, `arun` (the loops' and `GuardLe`'s components, `PreS` already
    sealed), `rU`, `rV`, `rM`, `inputLenLang`, `ValidPlain`, `ValidPair`.
- `GuardLe` itself is an `abbrev` whose components are sealed.
- **Output** (`DeepenSealed.out`): exit 0, 0 errors, 7.0 s.
- **Controls** (`DeepenSealControl.lean`): one `rfl` unfolding of each of the 35 definitions,
  first unsealed and then under the same attribute.
  - **Output** (`DeepenSealControl.out`): 35 errors, every one in the sealed section (lines
    > 126), one per sealed example. The unsealed section has none, so every unsealed goal closed
    and every sealed goal failed at its own goal.

### Inspection table (`evidence/inspection/`)

- `args.tsv` lists every argument of `rw`/`rwa`/`simp`/`simp only`/`simp_all`/`simpa`/`dsimp`/
  `unfold` and every `show`, with file and line (292 rows over `Deepen.lean` and `Savitch.lean`,
  extracted by `extract.py`).
- `kinds.out` gives the kind of every global constant among them (`Kinds.lean`). Every one is a
  **theorem**; no TCSlib, Mathlib or core definition is passed to `rw`/`simp`/`unfold`.

| constant | kind | uses |
|---|---|---|
| `Function.update_of_ne` | theorem | 20 |
| `Function.update_self` | theorem | 15 |
| `Function.update_idem` | theorem | 6 |
| `Function.update_apply` | theorem | 4 |
| `Function.comp_apply` | theorem | 3 |
| `zero_add` | theorem | 8 |
| `one_mul` | theorem | 3 |
| `dif_pos` | theorem | 4 |
| `dif_neg` | theorem | 4 |
| `if_pos` | theorem | 2 |
| `if_neg` | theorem | 3 |
| `Fin.ext_iff` | theorem | 4 |
| `Fin.val_mk` | theorem | 2 |
| `Complexity.logSpace_eq` | theorem | 3 |
| `Complexity.LogProg.indicator_eq_decide` | theorem | 2 |
| `Complexity.LogProg.astep_inc` | theorem | 2 |
| `Complexity.LogProg.astep_clr` | theorem | 1 |
| `Nat.sub_add_cancel` | theorem | 2 |
| `Complexity.Codec.stepRel_iff_mem` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.setSt_toV` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.outerSt_toV` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.rel_iff_orc` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.initO_iff_orc` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.accO_iff_orc` | theorem | 1 |
| `Complexity.LogProg.SavitchARM.noEdge_iff` | theorem | 1 |
| `pow_add` | theorem | 1 |
| `mul_comm` | theorem | 1 |
| `mul_assoc` | theorem | 1 |
| `decide_eq_false_iff_not` | theorem | 1 |
| `decide_eq_decide` | theorem | 2 |
| `Nat.size_eq_bits_len` | theorem | 1 |

The remaining arguments are:
- local hypotheses: `hσ`, `hw`, `hW`, `hj`, `hι`, `ho1 … ho7`, `hb3`, `o1L`, `o1S`, `o4T`, `o4W`,
  `o5S`, `o5W`, `o5C`, `e`, `e1`, `e2`, `e18`, `e21`, `f1`;
- inline `show … from rfl/dif_pos/dif_neg` equations about the file's own exits (`dpCbEx`,
  `dpCtEx`, `dpCt0`, `dpσE`);
- `dsimp only` with no lemmas (projections of `Fin.mk`).

`show` steps reduce only the file's own definitions, `Fin.val ⟨_, _⟩` and a β-redex
`(fun _ => 0) r`, which is allowed in a `show`. `simp_all` (in `dp_pre`) uses only the
hypotheses `D l = …`.

## 7. Duplication governance

### Screens (v3, one run at a time, `nice -n 10`, each on a frozen `git archive`)

- **Before** (`evidence/logs/screen-before.txt`): base `fd97df61`, the 19 files existing there.
  269 declarations, 96 pairs, 27,259 characters, none on `Savitch.lean`. It is **byte-identical**
  to `ch34-fill-deepen-screen-base.txt` (`diff` empty).
- **After** (`evidence/logs/screen-after.txt`): head `c7b179da`, all 20 files. 299 declarations,
  96 pairs, 27,259 characters. Its pair list equals the before list exactly (sorted `diff`
  empty), so there is **no new pair**, cross-file or within-file.
- Two intermediate after-screens each found one new within-file pair. Both were removed by
  refactoring:
  - `dpHl_le`/`dpHl_lt`, 61%, merged into one induction; that code was later replaced by
    `halvCount_loop`;
  - `dp_edge`/`dp_acc`, 50%: their shared preparation became `dp_block`.

### Semantic search (`evidence/logs/semantic-search.txt`, `evidence/runtime/semsearch.sh`)

- **Scope:** the tree at the head, plus the 16 PR heads contained in neither the campaign branch
  nor `main` (§1, disclosure 4).
- **Patterns:** by name (`dp_*`, `dpSt*`, `DpLb`, `dpD`) and by statement shape: update bounds,
  halving to zero, log against halving, register-file splits, clear chains, constant copies,
  single steps, copy/shift wrappers, block fits, oracle bridges.
- **Two hits replaced the fill's own helpers by published rows:**
  - `Complexity.Codec.halvCount_loop` (`Codec/Engine`, reachable through `Deepen`'s imports): the
    same `jz t; half t; inc c` loop as the fill's former private `dp_hl_run`. It is cited, and
    `dpHl`, `dpHl_succ`, `dp_hl_run` and their bounds are gone.
  - `Complexity.LogProg.register_update_le` (`Logspace/InputAccess`): the fill's former `dp_bd`.
    It is cited, and `dp_bd` is gone.

**Dispositions of the other hits, per private:**

| private | nearest hits | disposition |
|---|---|---|
| `dpρ_inj`, `dpρ_ne` | none (names); `exact?` closes `dpρ_inj` by Mathlib's `injective_of_le_imp_le` | kept: a one-line fact about the file's own map |
| `dp_mem`, `dp_rel`, `dp_initO`, `dp_accO` | `Correct.lean`'s `rel_orcN`, `initO_orcN`, `accO_orcN` (other oracle `orcN`, 4 deciders, proved by unfolding); the block fit's `fit_*` (a probe, not library) | kept: bridges for this file's 5-decider oracle and rerouting `σ`, through the published `_iff_orc` equations |
| `dp_pre`, `dp_inc`, `dp_clr` | `ExpBFS/Run`'s `inc_step`, `clr_step`, `step_of`; `SavitchARM/Run`'s and `PathHardMachine`'s `step_of` (each for its own machine's `St`) | kept: `D`-specific |
| `dpSt`, `dpSt_ρ`, `dpSt_own`, `dpSt_upd_ρ`, `dpSt_upd_own`, `dpSt_bd`, `dp_bd_blk` | no register-file split in the tree or the PR heads (the other machines use `St` structures with `toV`) | kept: `D`'s own register file |
| `dp_copy`, `dp_shl` | `cp_run`, `sh_run` (`SavitchARM/Run`, `ExpBFS/Run`: the same `copy_run`/`shl_run` instantiations for their machines) | kept: instantiations for `D` |
| `dp_cb_run` | `FragDec.clr_run` (a TM fragment), `Build/Loop`'s `emCall_clear_run` (private, TM) | kept: `D`'s straight-line clear chain |
| `dp_cT_run` | `SavitchARM/Run`'s `mul_run` (`A`'s multiplication loop, a rule 7 model) | kept: `D`'s unrolled copies (constant multiplier), not a loop |
| `dp_bits_logSpace` | `ISCountGenCorrect`'s `size_le_logSpace` (private, not citable); `Basic`'s `logSpace_le_size_succ` (cited) | kept: three facts, one cited |
| `dp_prep`, `dp_fit`, `dp_block`, `dp_edge`, `dp_acc`, `dp_body`, `dp_run` | `embed_guardLe` is used only in `ARMLoops` itself (the PR heads add none); the block fit's probe lemmas | kept: `D`'s runs; `dp_fit` is `fit_edge_block`'s shape, as the brief binds |

- **`exact?`** (`evidence/semantic/DeepenExact.lean` and `.out`, generator `mkexact.py`): each of
  the 27 private lemmas was restated as `example … := by exact?` just before its declaration, with
  a 400,000-heartbeat cap. 26 not closed; 1 closed (`dpρ_inj`, above).
- **Promotion requests: none.** No loop without a generic row remains. `dp_cb_run` and
  `dp_cT_run` are straight-line chains of `D`'s own labels.

## 8. Final checks

- **Final sweep** (`evidence/logs/final-sweep.log`, on the head): 196 modules, 196 with exit 0, 0 `error:` lines; total wall time 1,502 s; peak 2,952,008 KiB (`TCSlib/Complexity/TuringMachine/Build/CfgRecord`). Last line: `SWEEP COMPLETE: 196 modules`. An earlier full
  sweep on `362a6926` (`evidence/logs/dev/final-sweep-362a6926.log`) also passed 196/196. The only
  later change is `dp_block`'s docstring (`c7b179da`, for the style lint), so the sweep was
  re-run from scratch on the head.
- **Sorry warnings:** 25 warnings in 9 modules: ClassP/TimeConstructible 2, SpaceComplexity/Hierarchy 4, TuringMachine/Build/Loop 5, TuringMachine/Build/Primitives 3, TuringMachine/Build/RecordTable 4, TuringMachine/Build/Wrappers 2, TuringMachine/Composition 3, TuringMachine/Encoding 1, TuringMachine/Simulation 1. The base set less `savitch`'s is 25 entries in 9 modules: **equal, module by module**.
- **Axioms** (`evidence/logs/axioms.log`):
  ```
  'Complexity.savitch' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Complexity.savitch_of_logSpace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
  'Complexity.LogProg.SavitchARM.deepen_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- **Lint:**
  - `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`:
    `style_lint: 0 FAIL, 81 WARN over 112 files` (base: 0 FAIL, 80 WARN over 111). The one new
    WARN is check 8 on `Deepen.lean`: "1 public def(s) without a lemma beside them:
    DeepenContract". Check 8 wants a public lemma named `deepenContract_…`. Both names are pinned
    (`DeepenContract`, `deepen_contract`), and rule 3 forbids a fourth public declaration, so it
    stands. `deepen_contract` is the def's lemma in substance.
  - `python3 -I scripts/style_lint.py` on `Deepen.lean` and `Savitch.lean`: `0 findings in 2
    files`.
- **Public declarations added: exactly the three pins**:
  - `Complexity.LogProg.SavitchARM.DeepenContract`;
  - `Complexity.LogProg.SavitchARM.deepen_contract`;
  - `Complexity.savitch_of_logSpace_le`.

  The pins are verbatim; checked by text comparison against `DeepenRoute.lean.txt`. `savitch`'s
  statement is unchanged against the base. Everything else in `Deepen.lean` is private, under the
  `dp`/`Dp` prefixes: 43 private declarations (1 inductive, 15 definitions, 27 theorems).
- **File sizes:**
  - `SavitchARM/Deepen.lean`: 844 lines (new). The campaign lint's INFO is "> target 600"; it is
    under the 1,000-line limit.
  - `Savitch.lean`: 140 lines (base 118).
  - The facade, `SpaceComplexity.lean`: 266 lines (+3: one import, two module-list lines).
- **Owned regions only.** `git diff --stat fd97df61 HEAD` touches exactly
  `SavitchARM/Deepen.lean`, `Savitch.lean` and `SpaceComplexity.lean`. Nothing in `SavitchARM/*`
  (other than `Deepen`), `Machines/*` or `Codec/*` was edited.

## 9. Delivery contents (`fill-ch34-deepen.zip`)

- `REPORT.md` (this file);
- `source/`: the three modified files at the head;
- `patches/`: `git format-patch fd97df61..HEAD`;
- `fill-ch34-deepen.bundle`: `git bundle create … fd97df61..fill/ch34-deepen`; verify with
  `git bundle verify` on a clone holding `fd97df61`;
- `evidence/logs/`:
  - preflight, toolchain, cache store, roots, cache fetch, cache probe, manifest check;
  - the bootstrap and final sweep, with each module's `TIMED` line;
  - axioms, both lints, both screens, the semantic search and the open-PR note;
  - `dev/`, the first development checks;
- `evidence/seal/`: generator, sealed copy, controls, both outputs;
- `evidence/inspection/`, `evidence/semantic/`, `evidence/runtime/`: the inspection table and
  kinds, the `exact?` probe, and the timing, sweep and search scripts;
- `SHA256SUMS`, over every file of the zip except itself.
