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
