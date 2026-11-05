# The general `savitch`: the deepening design (design note, maintainer, 2026-11-04)

**What this is for.** Route (A) of `SAVITCH-route-design.md` (ruled 2026-10-27): iterative
deepening on the radius, reusing Hydroxyi's proved search (`SpaceComplexity/SavitchARM/*`) and the
general bridge `arm_decides_SPACE`. The route note said the deepening machine needs the search "as
a block over any acceptance decider, its lemmas stated for any program containing it", by
generalizing his machine, or else a 1–2k-line copy. This note designs that step and checks it
in Lean at the campaign tip (`711f5444`'s Lean, snapshot `oleans-leqc3`).

**The finding: nothing of his search needs restating.** One generic theorem about abstract
register machines transports *any* halting run of a machine `A` into a larger machine `D` that
contains `A`'s table as a block. `outerU_run`, `call_spec` and the rest stay exactly as they are,
stated for `A E`. `D` contains `A E` twice, once with the accepting-code decider and once with an
edge-code decider in its place. The theorem is proved in the probe
(`probes/EmbedProbe.lean.txt`, 0 diagnostics). It also fits `outerU_run` with decider `2`
rerouted to a fifth decider.

## 1. The embedding (proved in the probe)

```lean
/-- An instruction relabeled into a larger machine: registers along `ρ`, deciders along `σ`,
labels along `ι`, and an answer `b` replaced by a jump to the exit `k b`. -/
def Ins.embed (ρ : Fin m → Fin m') (σ : Fin d → Fin d') (ι : Λ → Λ') (k : Bool → Λ')
    (r₀ : Fin m') : Ins m d Λ → Ins m' d' Λ'      -- `.ret b ↦ .jz r₀ (k b) (k b)`; the rest by renaming

theorem AHalt.embed (hρ : Function.Injective ρ) (hD : ∀ l, D (ι l) = (A l).embed ρ σ ι k r₀)
    (hA : ∀ l r l', A l ≠ .valP r l' ∧ A l ≠ .valQ r l')
    (hBB : B ≤ B') (he : ∀ r', e r' ≤ B')
    (h : AHalt A (oracle ∘ σ) x (GuardLe A x B) (some l, v, none) b)
    (hv : Ext ρ e v v') :
    ∃ v₂', (∀ r', (∀ r, ρ r ≠ r') → v₂' r' = e r') ∧ (∀ r, v₂' (ρ r) ≤ B) ∧
      AReach D oracle x (GuardLe D x B') (some (ι l), v', none) (some (k b), v₂', none)
```

`Ext ρ e v v'` says that `v'` extends `v` along `ρ` and equals `e` off `ρ`'s range. So `D`'s
own registers (the deepening counter, the input-length bound) survive the block. A call's
virtual input is unchanged under renaming, because `callSegs` reads only the mode and the
argument words. `PreS` transfers because `ρ` is injective, which keeps `jeq`'s registers
distinct and the call arguments `Nodup`.

**Why `hA` (no `valP`/`valQ`):** an embedded validation failure halts `D` with `false` instead of
jumping to the exit. `SavitchARM.A E` has none. This is `A_noVal`, proved in
`probes/NoValProbe.lean.txt` by `cases l` and the table in `Machine.lean` itself.

**Where it must land (rule 10).** Our files may not unfold `astep`, `arun`, `PreS` or `AHalt`
(Hydroxyi's, in `Machines/ARM` and `Machines/ARMProof`). There is no eliminator for `AHalt` and
no per-instruction step equation, so the probe's proofs unfold all of them. The landed lemmas
therefore sit **beside those definitions**: an additive API in his `Machines` layer, which is the
2026-10-27 ruling's "the maintainer generalizes his layer, by PR and gate, FYI only". Its
contents:

| File (Hydroxyi's) | Added | Proof reads |
|---|---|---|
| `Machines/ARM` | the step equations `astep_inc`, `_dec`, `_clr`, `_half`, `_jz`, `_jodd`, `_jeq`, `_call`, `_ret`, `_valP`, `_valQ`, `_jeqIn`, `_jeqFst`, `_jeqSnd` (`A l = … → astep A o x (some l, v, r) = …`) | `astep` (same file) |
| `Machines/ARMProof` | `Ins.embed`, `Ext`, `preS_of_ins` (the five syntactic premises give `PreS`), `preS_embed`, `astep_embed`, `AHalt.embed` | `PreS`, `AHalt` (same file); `astep` only through the step equations; `arun` through `ARMRun`'s published `arun_succ`, `arun_halted` |
| `SavitchARM/Machine` | `A_noVal` | `A` (same file) |

The step equations also serve every later register machine written outside his files: today, a
new machine's run proofs can only unfold `astep`. About 250 lines in all; no statement of his
changes, nothing removed.

## 2. The deepening machine `D` (new file, ours: `SavitchARM/Deepen.lean` or `SpaceComplexity/SavitchGeneral.lean`)

`D : ARM 21 5 Lb'` with `Lb' = Lb E ⊕ Lb E ⊕ Own`, where `E` is any fixed index (the embedded
setup labels are dead code). The registers are `A`'s 18 registers along `Fin.castSucc` and three
of its own: the input length `n`, `ℓ = logSpace n`, and the radius `s`. The deciders are
`0 inputLenLang`, `1 initLang`, `2 acceptLang`, `3 stepLang` and `4 edgeLang` (§3). The two
blocks use `σ_edge` (`2 ↦ 4`) and `σ_acc` (the identity on `0..3`). On input `x`:
1. count `n` (decider `0`), compute `ℓ` (a halving loop), and set `s := 1`;
2. set `w := C·(s + ℓ + 1)` and `K := 2 ^ w` (the `ARMLoops` multiplication and shift loops),
   clear the block's registers to `outerSt s w 0 0 0`, and enter the edge block at `OU`;
3. on exit `true` (an edge code is reachable), set `s := s + 1` and repeat step 2. On exit
   `false`, re-enter `outerSt s w 0 0 0` in the accept block and answer its exit bit.

Here `C` depends only on `N`: it must give `codeK N · (s + logSpace n + 1) ≤ w` and
`configBound n s ≤ 2 ^ w`. Each block is one `AHalt.embed` of `outerU_run`. The loop's
correctness is an induction on `sp |x| + 1 - s`. Registers stay below `2 ^ (w·w)` with
`w = O(s + logSpace n)`.

## 3. The codec side (new mathematics, small)

- **The edge language.**
  ```lean
  def edgeLang (N) : Language Bool :=
    {y | ∃ x c s, y = pairEncode x (pairEncode (bits c) (bits s)) ∧
      ∃ C, Cfg.InWindow s C ∧ cfgCode s C = c ∧ ∃ i, |C.workTapePos i| = s}
  ```
  `edgeLang_mem : edgeLang N ∈ LOGSPACE`. There are two homes (decision 2):
  - **(a) a fifth mode `edge` of the codec machine `CA`** (`Codec/Machine`, Hydroxyi's). This is
    the natural one: the `init` mode already tests the head flag of one cell (`init_tail`); the
    edge mode tests the first and last cells' flags. It edits his machine's table and `CMode`,
    and every proof that cases on the mode.
  - **(b) a separate small decider** in our file: `validLang`'s decider, then a bit test at the
    head-flag positions of cells `±s`. This needs those positions as published facts about
    `cfgWord`; a pre-ship probe says whether they exist.
- **Window exactness**, `mem_iff_reach_of_noEdge`. It is `mem_iff_reach` with `hs : sp |x| ≤ s`
  replaced by "no edge code is reachable at level `w`". `(⇐)` is `mem_of_codePath`, which holds
  at any radius. For `(⇒)`: if no edge configuration is reachable, every reachable configuration
  is in the window with its heads strictly inside, by induction on steps (a head moves one cell,
  and writes land at old head positions). So an accepting branch is a `StepRel` path at radius
  `s`; shortcut it to a chain of length below `2 ^ w` and cut it with `reach_of_chain`.
- **A shortest-path lemma**: a `ReflTransGen` path through fewer than `K` vertices has a chain of
  length less than `K`. It is generic, so check Mathlib first.
- **Termination**, `noEdge_of_lt`: for `sp |x| < s`, no edge code is reachable. Every reachable
  configuration is in the window `sp |x|` (`runWith_take_inWindow` under `DecidesInSpace`).
- **A linear configuration count**: `configBound n s ≤ 2 ^ (C·(s + logSpace n + 1))`.
  `configBound_le` is the polynomial instance.

## 4. The assembly

`savitch S hS`: from `L ∈ NSPACE S`, take `N` deciding `L` in space `c·S`. `D` halts with
`decide (x ∈ L)`: by §2 and §3, the loop stops at some `s ≤ c·S|x| + 1`. Register values at
most `2 ^ (w·w)` have `O((S|x|)²)` bits, because `logSpace ≤ S` is `hS.1`. Conclude with
`arm_decides_SPACE` at `S·S` (`logSpace ≤ S ≤ S·S`). Constructibility is used only through
`hS.1`. The witness machine is never run, as route (A) intended.

## 5. Plan and sizes (ESTIMATE)

1. **API PR** (maintainer, §1's table): about 250 lines in three of Hydroxyi's files, all
   additive. Light gate (rule-10 seal of the new proofs, freeze, census, replay of the three
   files' downstream). FYI to Hydroxyi with the PR.
2. **Fill** (a brief after the API PR merges): §2 to §4, about 1.2–2.2k lines in new files,
   plus §3's edge decider, either about 0.3–0.5k in `Codec` (option (a)) or about 0.3–0.6k
   in our file (option (b)).

## 6. Decisions (the user's)

1. **The embedding instead of restating the search.** Recommended: it leaves every statement of
   his unchanged and adds only lemmas beside his definitions. The ruled alternative, his search
   restated for any program, would rewrite `Search`/`Recursion`/`Run`.
2. **The edge decider's home**: (a) a codec mode, or (b) a separate decider. Recommended: decide
   by the pre-ship probe of `cfgWord`'s published layout facts. Use (b) if they exist, otherwise
   (a).
3. **Agent for the fill**: by the soft rule, Codex for a first attempt.

## 7. Decided at pre-ship (2026-11-04): the edge decider is a codec mode

The rule (decision 2, user 2026-11-04) was a separate decider if `cfgWord`'s head-flag positions
are published, else a codec mode. The chunk-level facts are published (`getD_cfgWord_chunk`,
`chunkBit_tape`, `cellOf`'s head field), so the check is easy to state. Deciding it in logspace is
another matter: it needs the codec machine's parse of `⟨x, ⟨w, bits s⟩⟩` (the radius into a
register, the layout's base address) and its validity scan. A separate decider would rebuild both,
or embed `CA`'s partial run, which the API transports only for halting runs. So, by the rule:
**a fifth mode `edge` of `Complexity.Codec.CA`**, a maintainer API PR in Hydroxyi's `Codec` files
(the 2026-10-27 authorization; FYI only):
- `Langs`: `edgeLang N`, the codes at radius `s` of window-bounded configurations with some work
  head at `±s`;
- `Checks`: `EdgeChk` (valid, and some tape `i` with the head flag set at chunk `0`, offset
  `hH + 3i + 2`, or at chunk `2s`), and `edgeLang_iff`, from `validChk_iff`,
  `getD_cfgWord_chunk`, `chunkBit_tape` and `cellOf`;
- `Machine`: `CMode.edge`; after the validity scan, if `VAcc` holds, a loop over tapes. Set
  `U := A + 2(hH + 2)` and a down-counter to `k`; read the bit at `U`; copy `U`, add `4W · s`, read
  again; then `U += 6` and count down. It answers `true` at the first set flag and `false` at the
  end. With no work tape it answers `false`. New sites: copies (`A → U`, `U → Q1`, `S → T`), a
  scale (`Q1 += 4W · T`) and increment chains (`2(hH + 2)`, `6`, `k`), all within the label
  families' bounds;
- `Deciders`: `edge_tail` (as `init_tail`, by induction over tapes) and `edgeLang_mem`.

ESTIMATE: 400–600 lines. *Superseded (gate 91, minor 5):* as shipped (#184), the edge proofs read
the machine through #182's step equations and `preS_of_ins`, so #184 is stacked on #182 and lands
after it. The deepening fill's brief issues once both have merged.


## 8. The fill's route, pinned (2026-11-04, after #182 and #184 were staged)

The route probe is `probes/DeepenRoute.lean.txt`. It was elaborated against a clone with #182 and
#184 compiled on the campaign's Lean (`probes/DeepenRoute.out`): exactly the four `sorry` warnings
below, nothing else. It states the fill's new pieces and proves `savitch` from them.

| Statement (pinned) | What it says | Home (new files, ours) |
|---|---|---|
| `NoEdge N x s w` | no edge code is `Reach`able at level `w` from an initial code at radius `s` | `SavitchARM/Window` |
| `mem_iff_reach_of_noEdge (h : N.DecidesInSpace L sp) x s w hw hcb (hne : NoEdge N x s w)` | `mem_iff_reach`'s conclusion, with `sp |x| ≤ s` replaced by `NoEdge` | `SavitchARM/Window` |
| `noEdge_of_lt h x s w (hs : sp |x| < s)` | beyond the space bound no edge code is reachable | `SavitchARM/Window` |
| `configBound_le_pow N n s` | `configBound n s ≤ 2 ^ ((|Q| + 3 + 9k)(s + logSpace n + 1))` | `SavitchARM/Window` |
| `DeepenContract L sp` / `deepen_contract h` | some ARM with logspace deciders answers `x ∈ L` with register digits at most `C (sp |x| + logSpace |x| + 1)²`: `arm_decides_SPACE`'s hypothesis | `SavitchARM/Deepen` |
| `savitch_of_logSpace_le S (hS : ∀ n, logSpace n ≤ S n)` | `NSPACE S ⊆ SPACE (S · S)`; **proved in the probe** from `deepen_contract` and `arm_decides_SPACE`, with `K = C (c + 2)²` | `Savitch` |

`savitch` follows as `savitch_of_logSpace_le S hS.1`. **Constructibility is used only through
`logSpace ≤ S`**: iterative deepening never computes `S`. The probe's proofs also check the
arithmetic of the pins by hand:
- **The configuration count.** Its exponents add up to
  `|Q| + 3 + logSpace n + 6ks + 2k ≤ (|Q| + 3 + 9k)(s + logSpace n + 1)`.
- **Window exactness (⇒).** Take an accepting branch. If no prefix configuration has a head at
  `±s`, the prefixes form a `StepRel` path at radius `s`. Shortcut it below `configBound ≤ 2 ^ w`
  and cut it with `reach_of_chain`. Otherwise the first configuration with a head at `±s` is still
  window-bounded: the write lands at the old head position, which is inside. So it is a reachable
  edge code, against `NoEdge`.
- **Window exactness (⇐)** is `mem_of_codePath`, at any radius.
- **Termination.** A `Reach` witness unfolds to a `CfgStep` path from the initial configuration.
  Under `DecidesInSpace`, its heads stay at distance below `sp |x|` (visited cells, the halting
  budget), so no head reaches `±s`.

**The fill's work:** the four `sorry`s; the shortest-path lemma (check Mathlib first); and the
machine `D` of §2, built from `AHalt.embed_guardLe` (#182), the `ARMLoops` loops (`copy_run`,
`shl_run`, `halve_run`, …) and the deciders `inputLenLang`, `initLang`, `acceptLang`,
`stepLang` and `edgeLang` (`edgeLang_mem`, #184). The register bound comes from the last radius
`s ≤ sp |x| + 1`, where `w = C_w (s + logSpace |x| + 1)` and every register is at most
`2 ^ (w · w)`. ESTIMATE: 1.2–2.2k lines. The brief issues once #182 and #184 have merged, with its
pre-ship on the merged tree.

## 9. The pre-ship on the merged tree (2026-11-05, after #182, #184, #188, #189 and #190)

The probes are in `probes/`. They were elaborated against `oleans-led4` (the campaign's Lean
after #188 and #189), then again against `oleans-lcf3` (after #190, which changed
`Build/CfgRecord`, in the fill's import closure), with identical outputs (`probes/lcf3/`).

1. **§8's route probe is unchanged on the merged tree** (`DeepenRoute-merged.lean.txt`, `.out`):
   exactly its four `sorry` warnings.
2. **The window lemmas are mostly published already, in `ExpBFS/Radius` (Hydroxyi's).** That file
   searches growing radii for the exponential-time simulation. It proves that reachable codes are
   the codes of window runs (`rcode_iff`), that every run of a space-`sp` decider stays in the
   window `sp |x|` (`inWin_runWith_of_decides`), and the window run's extension laws
   (`WinRun.snoc`, `WinRun.last`, `inWin_init`, `coreSum_eq_of_code_eq`). The window route probe
   (`WindowRoute.lean.txt`) proves `noEdge_of_lt` and `mem_iff_reach_of_noEdge` from those lemmas,
   `mem_*Lang`, `cfgCode_lt`, `reflTransGen_of_reach`, `mem_of_codePath`,
   `Cfg.InWindow.core_bounds`, `inWindow_of_coreSum_eq`, `stepWith_eq_apply` and
   `DecidesInSpace.mem_iff_acceptsWithin_configBound`, plus six API statements (below). Sealed
   over 24 other-file definitions (`window-seal/`), it elaborates with only the two non-equation
   API stand-ins' `sorry` warnings. Its 48 controls all fail sealed; unsealed, 46 pass, and the two
   others are the recursive definitions' delta goals (`Reach`, `NDTM.runWith`).
3. **Revised pins.** Path shortening is done on codes, which lie below `2 ^ w` once
   `codeK N (s + logSpace |x| + 1) ≤ w`, so the configuration count is not needed:
   - `mem_iff_reach_of_noEdge` drops `hcb : N.configBound x.length s ≤ 2 ^ w`;
   - `configBound_le_pow` is dropped from the fill (it would also have had to read `configBound`'s
     value, which has no published equation);
   - `D`'s width is then `w = codeK N (s + ℓ + 1)` exactly.
4. **The API the route needs (six lemmas).** Each is proved at its home in
   `WindowApi.lean.txt` (0 diagnostics); `reach_of_reflTransGen` is proved there under a seal of
   `WalkLe` and `Reach`.

   | Home | Lemma | Owner | Covered by the 2026-10-27 exception? |
   |---|---|---|---|
   | `Build/CfgRecord` | `Cfg.InWindow.apply_of_lt`: an action applied to a window-`s` configuration whose heads are strictly inside `[-s', s']` (`s ≤ s'`) lands in the window `s'` (it also gives `ExpBFS`'s `inWin_stepWith`, at `s' = s + 1`) | the campaign | not needed |
   | `Codec/Bridge` | `stepRel_iff` (`Iff.rfl`) | Hydroxyi | yes (`Codec/*`) |
   | `SavitchARM/Reach` | `reach_of_reflTransGen`: a path of a relation whose steps stay below `K` is a `Reach K R i` witness when `K ≤ 2 ^ i`; from `reach_iff_walkLe` (one shortening argument in TCSlib, `walkLe_short`) and `reach_of_chain` | Hydroxyi | yes (`SavitchARM/*`) |
   | `Logspace/PathWalk` | `walkLe_zero_iff`, `walkLe_succ_iff` (`Iff.rfl`) | Hydroxyi | **no** |
   | `ExpBFS/Radius` | `rcode_iff_reflTransGen`, `winRun_iff` (`Iff.rfl`) | Hydroxyi | **no** |

   Without the last two rows, the fill would have to re-derive `rcode_iff` (path to run) and
   `walkLe_short` (shortening), because rule 10 forbids reading `RCode`, `WinRun` and `WalkLe`
   by their definitions. That is a ruling for the user (decision 4 below).
5. **What is left for the fill:** the machine `D` of §2, `deepen_contract`, and the two window
   lemmas in their probed form, about 1.0–2.0k lines (ESTIMATE).

**Decision 4, ruled by the user (2026-11-05): "Four Iff.rfl equations".** The exception extends
to the four `Iff.rfl` equations in `Logspace/PathWalk` and `ExpBFS/Radius`, FYI only. The six
lemmas land in one maintainer API PR with its gate and replay; the fill's brief issues after it
merges.

## 10. The block fit, and the API completed (2026-11-05, overnight)

**The fit.** `probes/BlockFit.lean.txt` (0 diagnostics, on the API branch's tree, sealed over 19
definitions) embeds `A E` in an abstract five-decider machine `D` with decider `2` rerouted to the
edge language. Entered at the outer search with the setup's registers, the block exits through
`k b`, with `b` exactly the deepening's question: whether some initial code reaches some edge code
by midpoint reachability at radius `s` and level `w`, in the codec's terms. It reads the search
through four more equations, which are the API's last rows:

| Home (Hydroxyi's, 2026-10-27 exception) | Lemma |
|---|---|
| `SavitchARM/Search` | `initO_iff_orc`, `accO_iff_orc` (`Iff.rfl`); `outerSt_toV` (the outer search's register file as `Function.update`s of `setSt`'s) |
| `SavitchARM/Recursion` | `rel_iff_orc` (`Iff.rfl`) |
| `SavitchARM/Setup` | `setSt_toV` (the setup's register file as `Function.update`s of zero) |

The register-file equations are proved through `Machine`'s published `St.toV_zero` and `St.upd_*`,
so they read `Machine`'s definitions under rule 10. With them, the fill's machine sets the
block's registers by clearing all eighteen and writing `rs`, `rw`, `rK`, `rU`, `rV`, `rM` in
that order. Its register file then matches `RegExt`'s target pointwise, with no register-distinctness
facts needed.

**The window lemmas are proved.** On the API branch, `probes/WindowRoute.lean.txt`'s two lemmas
close with no `sorry`. `probes/WindowModuleDraft.lean.txt` (163 lines, 0 diagnostics) is the module
`SavitchARM/Window` as library text, with docstrings and sketches. Whether it lands with the API PR
or goes to the fill as an input is for the user (decision 5).

**The API branch** (`lean/deepen-window-api`, local, eight commits, one per file): eleven lemmas
and one private helper, additive. Gate 96's pack and evidence are drafted in
`campaign/gates/96-deepen-api/`. The downstream replay is 72 modules.

**What remains for the fill:** the machine `D` (its own loops: the input length through decider
`0`, `ℓ`, the radius loop, the width and `2 ^ w`, the register resets), its run lemma by induction
on `sp |x| + 1 - s`, the register bound, and `deepen_contract`; `savitch_of_logSpace_le` and
`savitch` as probed in §8. ESTIMATE: 0.8–1.6k lines.

**Decision 5 (the user's):** land `SavitchARM/Window` with the API PR (the maintainer's proof,
gated with it), or give it to the fill as an input to land as is.

**Ruled, 2026-11-05 (morning).**
- **Decision 5:** the window module lands with the API PR. It is
  `SpaceComplexity/SavitchARM/Window.lean` on #196 (`lean/deepen-window-api`, head `89f4ebbc`),
  the draft of `probes/WindowModuleDraft.lean.txt` with the header options moved above the module
  docstring as in its siblings, and one import line plus one module-list entry in the facade
  `SpaceComplexity.lean`. Sealed over the window route's 24 definitions, it elaborates with 0
  diagnostics; `noEdge_of_lt` and `mem_iff_reach_of_noEdge` are on the standard axioms.
- **The fill's agent:** Claude (the user). The brief `ch34-fill-deepen-DRAFT.md` records both.
- **The API branch is pushed** and #196 is open against the campaign. Its replay, `replay-ldwa`, is
  the ten files' downstream closure, 73 modules chained from `oleans-lcf3`.
