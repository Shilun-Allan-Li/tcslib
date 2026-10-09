# §12 fill campaign — Epoch F1, Batch A: the embedding transformers (`Build/Embed.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/s12-f1-A`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `f7f4f0f7`), and never rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-s12-f1-A.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **13 audited-true statements** of the §12
machine-routine layer's bank-embedding module, in **tcslib**'s Arora–Barak
formalization. The statement gate closed after a three-round external
audit (`audits/routine-infra-{findings,r2-findings,r3-findings}.md`, loop
summary `audits/routine-infra-resolutions.md` — all in the repo; read
them). The audits left a near-complete proof plan: the round-3 report
proves the through-halt induction on paper, step by step. Two sibling
batches fill `Build/Seam.lean` and `Build/Catalog.lean` concurrently —
**you never touch those files**. In-repo proved precedents:
`Turing.captureAction`/`capture_run` and `Turing.emitAction`/`emit_run`
(`Build/Wrappers.lean` — the fixed-shape precursors: last-tape capture,
identity selection), `Cfg.mapState`/`Cfg.mapState_apply`
(`StateRenaming.lean`), and the `Simulation.lean` lockstep gadgets.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Embed.lean` — all 13 sorried
theorems, in this fill order (each later one leans on the earlier):

1. `embedSilentTM_runFrom` — the one-step commutation core, then
   `runFrom_comm_of_step`. Prove the two `embedSlot` glue equations first
   (`embedSlot ι (ι i) = some i`; `embedSlot ι j = none` off the range —
   `List.find?` + injectivity) as `private` lemmas; everything uses them.
2. `embedSilentTM_frame` — componentwise projection of 1.
3. `embedSilentTM_visitedByTapeHead` 4. `embedSilentTM_visitedByTapeHead_frame`
   — head-position projections of 1.
5. `embedSilentTM_spaceUsedByTape_cap` — capture growth via
   `FinTM.bufferTape_append`.
6.–9. `embedEmitTM_runFrom` / `_frame` / `_visitedByTapeHead` /
   `_visitedByTapeHead_frame` — the forwarding mirror of 1-4 (same core,
   `sink = none`; output is `pre ++ c.output` by append associativity).
10. `embedSilentRetTM_run` 11. `embedEmitRetTM_run` — the through-halt
   contracts; the **binding proof plan is quoted below**.
12. `embedSilentRetTM_visitedByTapeHead` 13. `embedEmitRetTM_visitedByTapeHead`
   — visited **equality** with the closed flavors at every time; the
   audit's direct host-to-host comparison (quoted below) is the route —
   do NOT derive these from 10/11 (they hold without `hc` and for
   nonhalting sources).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Embed`.
- Iterate on your file per edit. Final: your file with **zero `error:`
  lines and zero `sorry` warnings**, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`
  (the facade imports you).
- **Axiom prints**: `#print axioms Turing.<name>` for all 13 filled
  theorems on the final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  `sorryAx` must not appear: this batch has **no sanctioned admitted
  dependency**.

## Ground rules (binding)

1. **File ownership.** Only `Build/Embed.lean`, and only the 13 targets'
   proofs plus `private` helpers. Shared wishes go under "Requested shared
   lemmas" in `REPORT.md` with a `private` local copy. List every new
   declaration — the epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere. Docstring sketch appendices allowed,
   flagged.
3. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
4. No touching sorries outside your file. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.
7. **Continuation budget**: 13 targets sharing one core. If your budget
   exhausts, deliver a partial zip whose `REPORT.md` states exactly which
   targets are proved, which `private` helpers remain `sorry` (allowed
   **only** in a partial delivery, each listed), and where the frontier
   is — the maintainer issues a continuation brief.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/routine-infra-r3-findings.md` (the through-halt proof plan
for targets 10-11; `E` is the flavor's configuration transport, `R` its
returning machine):

> 2. **Positive time follows, and the equivalence is precise.** [...] under
>    **both** `hlive` and `hhalt`,
>    `c.state ≠ none ⟺ 0 < T`.
> 3. **The same action is executed completely.** [...] Injectivity of `ι`
>    gives `embedSlot ι (ι i) = some i`; the transported selected tapes and
>    heads therefore supply exactly the source's work symbols. The input
>    position also agrees. Consequently both machines select the same
>    source action. `embedActionCore` copies its input movement and every
>    selected work-tape write and movement. Other frame tapes receive no
>    write or movement. In the suppressing case, `hcap` keeps capture
>    outside the selected bank: no emission leaves capture unchanged, while
>    emission of a bit appends that bit at the old word length, by
>    `bufferTape_append`; physical output remains `out₀`. In the forwarding
>    case, output becomes `pre ++` the new source output, by list-append
>    associativity. `Action.apply` performs these effects regardless of
>    whether the successor is halted. Only the successor control differs.
> 4. **Induct up to the last live time.** At zero, `runFrom_zero` gives the
>    required transported equality. If `t + 1 < T`, `hlive` makes the
>    source live at both `t` and `t + 1`. [...] the induction hypothesis
>    and `runFrom_succ_eq_step'` yield the transported equality for
>    `t < T`.
> 5. **Execute the final step.** Since `0 < T`, the predecessor satisfies
>    `T - 1 < T` and `(T - 1) + 1 = T`. The source is live there by
>    `hlive`, so step 3 applies. Its successor is `none` by `hhalt`, hence
>    `Option.elim` now selects `Sum.inr ()`. [...] At every earlier time,
>    step 4 and `hlive` put control in `some (Sum.inl q)`, distinct from
>    `some (Sum.inr ())`. This proves the first-visit clause.

From `audits/routine-infra-r2-findings.md` (the route for targets 12-13):

> **True without `hcap`.** Compare the two host machines directly: their
> live actions have identical non-control effects, and after a halt their
> respective halted state and return anchor are both stationary; if
> initially halted, both remain halted. This proof does not require the
> false run contract or source/capture separation. [...] It also covers
> runs that never halt.

The round-2 S8 trace (one-state emit-and-halt source: capture word
`[false,true]`, head 2, state `some (Sum.inr ())` at time 1) is the
smallest through-halt check — your proof of 10 must make it a `rfl`-grade
instance, though you need not state it.

## Out-of-scope sorries you will see (leave untouched)

Everything in `Build/Seam.lean` (batch F1B) and `Build/Catalog.lean`
(batch F1C + epoch F2); the chapter-3/4 statement surfaces
(`Diagonalization/*`, `ClassOracle/*`, `SpaceComplexity/*`,
`ClassPSPACE/*`, `Formulas/QBF*`, `TuringMachine/NDCodes.lean`,
`TuringMachine/Oracle*.lean`, `TuringMachine/NondeterministicSpace.lean`,
`SpaceComplexity/ZeroSpace.lean`, `CounterProgRun`'s S9).

## REPORT.md checklist

- [ ] 13/13 filled (or the partial frontier per ground rule 7).
- [ ] Base commit hash; every new `private` declaration listed.
- [ ] The glue equations and the step-3 component check identified as
      lemmas (the epoch audit will look for them by role).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:`, zero `sorry` in your file) +
      facade check + 13 axiom prints (at most the standard triple; no
      `sorryAx`).
- [ ] Diff touches only `Build/Embed.lean`.

## Known pitfalls at this pin (hard-won)

- `embedSlot` unfolds to `List.find?` over `List.finRange` with a
  `decide (ι i = j)` predicate: use `List.find?_eq_some`-style reasoning
  plus `Finset`-free injectivity; `simp [embedSlot, List.find?]` alone
  thrashes. Prove the two glue equations once, `private`.
- `Fin` case analysis: `fin_cases j` or `match` on `embedSlot ι j`; after
  `cases hs : cfg.state`, `dsimp only` before rewriting.
- `Option.elim` on the successor: `Option.elim none a f = a` and
  `Option.elim (some x) a f = f x` are definitional — `rfl` after the
  right `cases`.
- `Cfg` structure updates `{ c with state := … }`: beware eta — two
  configurations agree iff all five fields do; use `Cfg.ext`-style
  congruence if available, else `cases c` and `rfl`-chase.
- `Cfg.mapState` lives in `StateRenaming.lean` (already imported);
  `Cfg.mapState_apply` is the one-step commutation workhorse.
- `Function.update_of_ne` (not `update_noteq`); avoid bare `simp` with
  folded forms; `omega` needs beta-reduced, non-`Fin`-projection goals.
- `MultiTapeTM.runFrom_succ_eq_step'`/`…_step` peel opposite ends; work
  tapes are ℤ-indexed `Option Symbol` via `Function.update`.
- Visited sets: `visitedByTapeHead` is a `Finset.image` over
  `Finset.range (t+1)` — equalities of trajectories give equalities of
  images by `Finset.image_congr`-style reasoning.
