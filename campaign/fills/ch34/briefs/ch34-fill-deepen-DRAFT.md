# Ch3–4 fill campaign — the general Savitch theorem by iterative deepening (`Complexity.savitch`, `SpaceComplexity/Savitch.lean`, new `SavitchARM/Deepen.lean`)

> **DRAFT, not issued** (maintainer, 2026-11-05 overnight). It issues after the deepening API PR
> (gate 96) merges, with its pre-ship re-run on the merged tree and the measured items (`@TBD@`)
> filled in. Ruled by the user, 2026-11-05:
> - **decision 5:** `SavitchARM/Window` lands with the API PR (#196), so this fill cites it;
> - **the agent:** Claude.
>
> **A single fill** (addendum v2.6, Parts 1 and 2; of Part 3 only its one-Lean rule and its
> no-stop rule, items 5 and 7). Deliver a checkpoint zip after each checkpoint: the session may
> end at any time.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out branch
  **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit contains:
  - **the search** you embed: `Complexity.LogProg.SavitchARM.A E : ARM 18 4 (Lb E)`, its outer
    search `outerU_run`, `A_noVal`, and the codec's deciders and their memberships
    (`initLang_mem`, `acceptLang_mem`, `stepLang_mem`, `edgeLang_mem`, `inputLenLang_mem`);
  - **the embedding** (#182): `Complexity.LogProg.Ins.embed`, `RegExt`, `preS_of_ins`,
    `preS_embed`, `AHalt.embed`, `AHalt.embed_guardLe`, and the step equations `astep_inc` …
    `astep_jeqSnd` (`Machines/ARM`);
  - **the edge language** (#184): `Complexity.Codec.edgeLang`, `mem_edgeLang`, `edgeLang_mem`;
  - **the deepening API** (#196, gate 96):
    - `Cfg.InWindow.apply_of_lt`, `stepRel_iff_mem`, `walkLe_zero_iff`, `winRun_iff`,
      `rcode_iff_reflTransGen` and `reach_of_reflTransGen`;
    - `rel_iff_orc`, `initO_iff_orc` and `accO_iff_orc`;
    - `setSt_toV` and `outerSt_toV`;
    - the window module `SavitchARM/Window`: `NoEdge`, `noEdge_of_lt`, `mem_iff_reach_of_noEdge`;
  - the generic loops of `Machines/ARMLoops` (`move_run`, `move2_run`, `dmove_run`, `sub_run`,
    `halve_run`, `copy_run`, `shl_run`), `inputLength_loop` (`Logspace/InputAccess`), the run
    algebra of `Machines/ARMProof` (`AReach.refl`, `.trans`, `.step`, `.single`, `.halt`,
    `.mono`, `AHalt.step`, `.ret`, `.mono`), and `arm_decides_SPACE` (`Machines/ARMWidth`);
  - the fill-environment addendum `campaign/standards/fill-environment-addendum.md` (**v2.6**) and
    the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/ch34/inputs/ch34-fill-deepen/`):
    - the route probe with the pins and the assembly (`DeepenRoute.lean.txt`);
    - the block fit (`BlockFit.lean.txt`): the template for both blocks;
    - the import probe, the order list, the base sorry set and the screen base (`@TBD@`).

  The design note is `campaign/items/ch34/savitch-general/SAVITCH-deepening-design.md` (§2, §8–§10).
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule. Fetch
  the cache for your roots only; never the unfiltered `lake exe cache get`. If Lean never runs, do
  not draft proofs blind: deliver the environment report only.
- **Branch at exactly that commit**: `git checkout -b fill/ch34-deepen @ANCESTOR@`;
  `git rev-parse HEAD` must print `@ANCESTOR@`. Never rebase, merge or cherry-pick.
- **Delivery is by zip** (`workflow.md` §4): `fill-ch34-deepen.zip`, with the same contents as
  NF's fill:
  - `REPORT.md`, the full modified source, a `git format-patch` series against your base and a
    git bundle;
  - the environment logs (`evidence/logs/`), the bootstrap and final sweep logs with each
    module's time and maximum memory, and the axiom log;
  - the seal test's source, its controls and both outputs;
  - both screen outputs and `SHA256SUMS`.

  **Checkpoint zips** `fill-ch34-deepen-cp<N>.zip`, one per checkpoint below.

## What this is

**Savitch's theorem for every `S ≥ logSpace`** ([AB09, Theorem 4.14]; [Sav70]):
`NSPACE S ⊆ SPACE (S · S)`. The book assumes `S` space-constructible and computes the radius
`S(|x|)` first. Here no radius is computed: the machine **deepens**. At `s = 1, 2, …` it asks
Savitch's midpoint search whether a configuration with a work head on the window's edge `±s` is
reachable:
- if one is, the space bound exceeds `s`, so it tries `s + 1`;
- if none is, membership is decided by the same search at radius `s` (window exactness).

The search stops by `s = sp |x| + 1` (termination), and every register stays below
`2 ^ (w · w)` with `w = codeK N · (s + ℓ + 1)` and `ℓ` the input length's binary length, so the
space is `O((sp |x| + logSpace |x| + 1)²)`.

**Where it stands.**
- `Complexity.savitch` is `sorry` (`Savitch.lean`).
- `PSPACE = NPSPACE` is proved directly, at the polynomial level, by the same search.
- The design's pieces are in place:
  - the search proved for any oracle (Hydroxyi);
  - the embedding of a block into a larger machine (#182) and the edge language (#184);
  - the API (#196).
- The maintainer's probes prove the window lemmas and the block fit outright, and `savitch` from
  `deepen_contract`.

**This fill writes one machine, `D`, and its correctness.** **Proved modulo, exactly:** none. A
complete delivery has no `sorryAx` in `Complexity.savitch`.

## Owned regions and targets (modify these and nothing else)

- **`TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean`** (new, yours): the machine `D`, its
  run, the pinned `Complexity.LogProg.SavitchARM.DeepenContract` and `deepen_contract`, with
  private helpers under the prefix `dp_` (`Dp`/`dp` for types and definitions).
- **`TCSlib/Complexity/SpaceComplexity/Savitch.lean`:**
  - **(a)** its imports: add exactly `TCSlib.Complexity.SpaceComplexity.SavitchARM.Deepen`;
  - **(b)** the pinned `Complexity.savitch_of_logSpace_le`, before `savitch`, with the route
    probe's proof;
  - **(c)** `savitch`'s body: `savitch_of_logSpace_le S hS.1`;
  - **(d)** the public text:
    - `savitch`'s docstring, whose sketch describes the old explicit-stack route: replace it with
      the deepening's;
    - the module docstring's **Status** and **Design** paragraphs.

    Public-facing text only: no campaign labels, gate or round names, `audits/` or `campaign/`
    paths, or dated rulings.
- **The facade `TCSlib/Complexity/SpaceComplexity.lean`:** the import line for `Deepen` beside
  `SavitchARM.Correct`'s, and one line in its module list.

**Targets:** `deepen_contract` and `savitch`, whose statement is frozen.

### The pinned statements (binding; `DeepenRoute.lean.txt`)

```lean
def DeepenContract (L : Language Bool) (sp : ℕ → ℕ) : Prop :=
  ∃ (m d : ℕ) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (D : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool), (∀ j, As j ∈ LOGSPACE) ∧ ∃ C : ℕ, ∀ x : List Bool,
      AHalt D (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
        (fun a => PreS D x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤
          C * (sp x.length + logSpace x.length + 1) ^ 2)
        (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)

theorem deepen_contract {N : FinNDTM Bool} {L : Language Bool} {sp : ℕ → ℕ}
    (h : N.DecidesInSpace L sp) : DeepenContract L sp

theorem savitch_of_logSpace_le (S : ℕ → ℕ) (hS : ∀ n, logSpace n ≤ S n) :
    NSPACE S ⊆ SPACE fun n => S n * S n
```

`DeepenContract` is `arm_decides_SPACE`'s hypothesis. **These three are the only new public
declarations.**

## The route (binding where it names a row; the rest is the recommended shape)

**The deciders** (binding): `As := ![inputLenLang, initLang N, acceptLang N, stepLang N,
edgeLang N]` (five; each in `LOGSPACE` by its `_mem` lemma). The oracle is the indicator family,
as in `DeepenContract`.

**The blocks** (binding): `D` holds `A E`'s table twice, for one fixed `E` (the setup labels are
dead code):
- **the edge block**, through `σEdge := ![0, 1, 4, 3]`;
- **the accept block**, through `σAcc := ![0, 1, 2, 3]`.

Each block is the image of `Ins.embed ρ σ ι k r₀`, with `ρ` an injective register map and `k`
the block's two exits into `D`'s own labels. **Each block's run is one `AHalt.embed_guardLe` of
`outerU_run`, with `A_noVal`, exactly as `BlockFit.lean.txt`'s `fit_edge_block`.** Copy that
proof's shape for both blocks:
- the oracle reads through `initO_iff_orc`, `accO_iff_orc`, `rel_iff_orc`, `stepRel_iff_mem`
  and `indicator_eq_decide`;
- the entry registers through `setSt_toV` and `outerSt_toV`;
- the block's answer is converted to the codec's terms by `decide_eq_decide`.

**Never re-prove the search, and never unfold `A`, `outerSt`, `InitO`, `AccO` or `Rel`.**

**The entry registers.** Before each block, clear all eighteen block registers, then write `rs`,
`rw`, `rK`, `rU`, `rV`, `rM` in that order: `s`, `w`, `2 ^ w`, `0`, `0`, `0`. The register file
is then `setSt_toV`'s and `outerSt_toV`'s `Function.update` chain through `ρ`, pointwise, by
`Function.update_apply` and `ρ`'s injectivity, with no register-distinctness facts needed. Keep
`n`, `ℓ`, `s` and `w` in `D`'s own registers, off `ρ`'s range: a block may change every register
of its own.

**`D`'s own loops** (recommended):
1. `n := |x|` by `inputLength_loop` with decider `0`;
2. `ℓ :=` the binary length of `n`, plus one, with your own halving loop;
3. `s := 1`;
4. the body at `s`:
   - `w := codeK N · (s + ℓ + 1)`, by `copy_run`s (`codeK N` is a constant of `N`);
   - `2 ^ w` by `shl_run` on a register holding `1`;
   - the register reset, then the edge block;
   - on `true`, `s := s + 1` and repeat the body;
   - on `false`, the reset again, then the accept block, whose exit bit is `D`'s answer.

`D`'s own instructions run through the step equations `astep_*` and `preS_of_ins`, never by
unfolding `astep` or `PreS`.

**Correctness.** Both window lemmas are published (`SavitchARM/Window`):
- `noEdge_of_lt`: for `sp |x| < s`, `NoEdge N x s w`;
- `mem_iff_reach_of_noEdge`: under `NoEdge`, the accept block's question is `x ∈ L`.

The edge block's answer is `false` exactly when `NoEdge` holds (its proposition is `NoEdge`'s
body). So by induction on `sp |x| + 1 - s`, `D` answers `decide (x ∈ L)` from the body at any
`s ≥ 1`, and the loop runs at most `sp |x| + 1` times.

**The register bound.** Every radius reached has `s ≤ sp |x| + 1`, so
`w ≤ codeK N · (sp |x| + logSpace |x| + 3)`:
- every block register stays at most `2 ^ (w · w)` (`embed_guardLe`'s second conjunct);
- `D`'s own registers are at most `max |x| (2 ^ w)`;
- so `(Nat.bits (v + 1)).length ≤ w · w + 1 ≤ C (sp |x| + logSpace |x| + 1) ^ 2` for a
  constant `C` of `N`.

State the guard as `GuardLe D x (2 ^ (w_max · w_max))` along the run, then convert it to the
contract's form.

**Edge cases that must stay true:**
- `x = []`: `n = 0`, `ℓ = 1`;
- `N.k = 0`: no edge configuration exists, and the first edge block answers `false`;
- `sp |x| = 0`: the loop stops at `s = 1`;
- the halving loop at `n = 0`.

## Gate guidance (binding)

- **Gate 96** (the API): the eleven lemmas and the window module are the route. Cite them; never
  restate one.
- **The 2026-10-27 ruling:** the search is reused, not restated. Nothing in `SavitchARM/*`,
  `Machines/*` or `Codec/*` is yours to edit.

## Ground rules (binding)

1. **File ownership:** only the regions above.
2. **Statement freeze** over `savitch`; the pins exactly as given.
3. **No new public declaration** beyond the three pins.
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports:** `Deepen` imports exactly `SavitchARM.Correct`, `SavitchARM.Window` and
   `Machines.ARMLoops` (`@TBD@`: the import probe fixes the list).
7. **One proof per shared argument.** These are models to read, not to copy:
   - the search's own setup (`setup_run`, `ld_run`, `pw_run`, `mul_run`, `sh_run`), which is
     `A`'s;
   - `ExpBFS`'s radius iteration (`iter_run`, `ExpBFS/Main`; a multi-tape register machine);
   - `ExpBFS/Run`'s loops, `lg_run` and `hv`/`lgv`.

   Use the generic loops. If you need a loop with no generic row, write it once, as a private, and
   list it as a promotion request.
8. **Size:** no cap; report the line counts.
9. **Continuation budget:** a partial is expected and fine; an unreported gap is not.
10. **The pinned base, and no unfolding** (user, 2026-10-16; scope 2026-10-23):
    - other files' TCSlib definitions are read only through their published equations: `A`,
      `outerSt`, `setSt`, `St.toV`, the register names, `InitO`, `AccO`, `Rel`, `Reach`,
      `StepRel`, the code languages, `astep`, `arun`, `PreS`, `AHalt`, `AReach`, `Ins.embed`,
      `RegExt`'s fields through its constructor and projections, and
      `MultiTapeTM.indicator` through `indicator_eq_decide`;
    - core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are never
      passed to `simp`, `rw` or `unfold`;
    - your own `D` may be unfolded, but prefer its table equations;
    - **self-check by both methods:**
      - a seal test with controls, extending `BlockFit.lean.txt`'s 19-definition seal by
        `astep`, `arun`, `GuardLe`'s components and the loops' definitions;
      - an inspection table of every `rw`/`simp`/`unfold`/`show` argument.

## Checkpoints

1. `D`'s labels and table, `As`, the oracle bridges (`fit_*` as in the block fit), `D`'s table
   equations and `PreS` for its own instructions.
2. The setup loops: `n`, `ℓ`, `s := 1`, with their runs.
3. The body's arithmetic: `w`, `2 ^ w`, the register reset and its `RegExt`.
4. The edge block's run (`fit_edge_block`'s shape) and the accept block's.
5. The loop: `D` halts with `decide (x ∈ L)` from the body at every `s ≥ 1`, by induction on
   `sp |x| + 1 - s`.
6. The register bound, and the guard in the contract's form.
7. `deepen_contract`.
8. `Savitch.lean`: `savitch_of_logSpace_le`, `savitch`, the public text, the facade lines.

Add no new admission: a helper is inserted only once proved.

## Duplication governance (binding)

Run the v3 screen before and after, one run at a time, under `nice -n 10`, each on a frozen copy
of its commit. The population (`@TBD@` files) is:
- your files;
- `SavitchARM/*`;
- `Machines/ARM`, `ARMProof`, `ARMLoops` and `ARMWidth`;
- `Logspace/InputAccess`, `Codec/Bridge` and `ExpBFS/Radius`;
- the hazards `ExpBFS/Main`, `ExpBFS/Run` and `ExpBFS/Machine`.

The semantic search is required: for every new private lemma, search the tree and every open PR
branch by name and statement, and pose it to `exact?`.

## Environment and verification

- Lean 4 v4.25.0; the cache for your roots only; **never `lake build`**;
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Bootstrap:** the order list (`@TBD@` modules); the base sorry set (`@TBD@`), where yours is
  `savitch`'s.
- **Final checks:**
  - every module of the order list: zero errors, sorry warnings exactly the base's less
    `savitch`'s;
  - the axiom prints: `savitch`, `savitch_of_logSpace_le` and `deepen_contract` on
    `[propext, Classical.choice, Quot.sound]`;
  - lint: `campaign_style_lint.py` 0 FAIL on `SpaceComplexity`, and the policy linter on your
    files.

## REPORT.md checklist

- [ ] The preflight, the cache and the bootstrap (per-module time and memory); the base hash.
- [ ] The checkpoints reached, one zip each.
- [ ] `D`'s labels, registers (with `ρ`'s map), deciders and loops, and each block's fit.
- [ ] `C`, term by term.
- [ ] The edge cases, each with the lemma that covers it.
- [ ] Rule 10: the citations, the seal with its controls and both raw outputs, the inspection
      table.
- [ ] Duplication: both screens, every new pair with a disposition, the semantic search per
      private.
- [ ] File sizes, the final sweep tail, the axiom prints and the lint lines.
