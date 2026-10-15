# §12 fill campaign — Epoch F1, Batch B: seam composition and the release adapter (`Build/Seam.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/s12-f1-B`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `f7f4f0f7`), and never rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-s12-f1-B.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **11 audited-true statements** of the §12 layer's
seam-composition module. The statement gate closed after a three-round
external audit (`audits/routine-infra-{findings,r2-findings,r3-findings}.md`,
summary `audits/routine-infra-resolutions.md` — read them); the round-2
and round-3 reports verify the exact lockstep decomposition you will
formalize. Two sibling batches fill `Build/Embed.lean` and
`Build/Catalog.lean` concurrently — **you never touch those files**.
In-repo proved precedents: `Cfg.mapState`/`Cfg.mapState_apply`
(`StateRenaming.lean`), `MultiTapeTM.runFrom_add` and the
`runFrom_comm_of_step` family, `Cfg.ofWords` (`Build/Convention.lean`).

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Seam.lean` — all 11 sorried
theorems. **Fill the general-configuration trio first; the canonical
statements are its instances** (the audited design — do not prove the
canonical ones independently):

1. `seamCompTM_run_ofCfg` — the three-segment decomposition (quoted
   below): left `Sum.inl` lockstep under the cut, one stationary silent
   write-free dispatch step (fixes every non-control field of an
   **arbitrary** configuration), right `Sum.inr` lockstep from
   `c₁.mapState (fun _ => entry)`.
2. `seamCompTM_firstReturn_ofCfg` — state projection of the segments +
   constructor disjointness + transported phase-two cut.
3. `seamCompTM_visitedByTapeHead_ofCfg` — trajectory split over
   `Finset.range`; the dispatch step is stationary at a point both
   phases already visit.
4. `seamCompTM_run` 5. `seamCompTM_firstReturn`
6. `seamCompTM_visitedByTapeHead` — instances of 1-3 at
   `Cfg.ofWords`, via the identity
   `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w` (prove it once,
   `private` — it should be definitional or near).
7. `seamCompTM_spaceUsedByTape_le_add` 8. `seamCompTM_spaceUsed_le_add`
   — cardinalities/sums over 6 (`Finset.card_union_le`, sum over tapes).
9. `seamCompTM_spaceUsedByTape_le_max` — the disjointly-owned-tapes max:
   the idle phase's singleton `{0}` is contained in the owner's visited
   set (both phases' seams start at the origin).
10. `seamReleaseTM_firstReturn` — the fresh step applies the anchor's
    action verbatim (`Cfg.mapState_apply` at the constant relabeling),
    then `Sum.inr` lockstep; time zero excluded by constructor
    disjointness (`Sum.inl () ≠ Sum.inr anchor`).
11. `seamReleaseTM_visitedByTapeHead` — step-for-step trajectory
    agreement (the fresh step and every `Sum.inr` step apply exactly
    `M`'s action at the carried state).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Seam`.
- Iterate on your file per edit. Final: your file with **zero `error:`
  lines and zero `sorry` warnings**, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`
  (the facade imports you).
- **Axiom prints**: `#print axioms Turing.<name>` for all 11 filled
  theorems on the final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  no `sorryAx`: this batch has **no sanctioned admitted dependency**.

## Ground rules (binding)

1. **File ownership.** Only `Build/Seam.lean`, and only the 11 targets'
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
7. **Continuation budget**: 11 targets over one decomposition. On
   exhaustion, deliver a partial zip whose `REPORT.md` states what is
   proved, which `private` helpers remain `sorry` (allowed **only** in a
   partial delivery, each listed), and the frontier — the maintainer
   issues a continuation brief.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/routine-infra-r2-findings.md`, "General seam derivation and
state plumbing" — the two identities your induction must produce:

> Under the general seam hypotheses, induction gives the following two
> full-configuration identities:
>
> (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t
>   = (M₁.runFrom c₀ t).mapState Sum.inl                 (0 ≤ t ≤ T₁),
>
> (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) (T₁+1+t)
>   = (M₂.runFrom (c₁.mapState (fun _ => entry)) t).mapState Sum.inr
>                                                        (t ≥ 0).
>
> The intervening transition has zero head movements, no writes, and no
> output. Since `c₁.state = some exit`, constant state mapping really does
> produce `some entry`; it is not an attempt to revive `none`. Splitting
> the inclusive time interval into `0,…,T₁` and `T₁+1,…,T₁+1+T₂` proves
> visited-set **equality** with the union, hence the advertised
> containment. Projection onto states proves the inherited cut.
>
> The canonical instances follow by substituting
> `c₀ := Cfg.ofWords start w₀`, `c₁ := Cfg.ofWords exit w₁`,
> `c₃ := Cfg.ofWords q₂ w₂` and using the definitional identity
> `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w`.
> Thus all three canonical contracts are genuine specializations. Taking
> cardinalities and then summing recovers the canonical additive space
> bounds. For the canonical maximum bound, the idle singleton `{0}` is
> contained in the other phase's visited set.
>
> For release, the fresh state is in `Unit ⊕ S`, whereas the returning
> embeddings use `S ⊕ Unit`. These sums serve different purposes and are
> wired correctly. A released left phase exits at `Sum.inr anchor`; [...]
> The constant-map compositions preserve every data field, and the right
> phase's fresh constructor removes the zero-time cut obstruction.

The round-2 S7 trace (states `q,r`; word `[true]` written before any
dispatch; first re-arrival at time 2) and S9 trace (displaced head `7`,
output `[true]` crossing dispatch intact) are the smallest checks — your
proofs must make them instances, though you need not state them.

Also binding (round-2 assessment of target 3): the visited containment
has **no phase-two endpoint hypothesis, and none is needed** — do not
introduce one.

## Out-of-scope sorries you will see (leave untouched)

Everything in `Build/Embed.lean` (batch F1A) and `Build/Catalog.lean`
(batch F1C + epoch F2); all chapter-3/4 statement surfaces
(`Diagonalization/*`, `ClassOracle/*`, `SpaceComplexity/*`,
`ClassPSPACE/*`, `Formulas/QBF*`, `TuringMachine/NDCodes.lean`,
`TuringMachine/Oracle*.lean`, `TuringMachine/NondeterministicSpace.lean`).

## REPORT.md checklist

- [ ] 11/11 filled (or the partial frontier per ground rule 7); the
      general-trio-first derivation order confirmed (canonical = instances).
- [ ] Base commit hash; every new `private` declaration listed (the
      `ofWords`/`mapState` identity and the two lockstep lemmas expected).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:`, zero `sorry` in your file) +
      facade check + 11 axiom prints (at most the standard triple; no
      `sorryAx`).
- [ ] Diff touches only `Build/Seam.lean`.

## Known pitfalls at this pin (hard-won)

- `seamCompTM`'s dispatch branch matches on `Sum.inl s` with
  `if s = exit`: after `cases`, `dsimp only` then `split` — the
  `DecidableEq S₁` instance is a binder, don't `decide`.
- The dispatch action `⟨0, fun _ => (none, 0), none, some (Sum.inr entry)⟩`
  fixes every field of `Action.apply` — prove a `private`
  "stationary-silent-write-free apply = set state" lemma once.
- `Cfg.mapState` with a constant function sends `some exit ↦ some entry`
  via `Option.map` — `Option.map_some`.
- `Cfg` equality: `cases`-and-`rfl` or field-congruence; beware eta.
- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare `simp`
  with folded forms; `omega` needs beta-reduced goals.
- `MultiTapeTM.runFrom_add` splits at `T₁`, then at `1`:
  `T₁ + 1 + T₂ = (T₁ + 1) + T₂` — fix the association before `runFrom_add`.
- Visited sets are `Finset.image` over `Finset.range (t+1)`: for the
  split use `Finset.range_add`-style decompositions or
  `Finset.image_union` after splitting the index set.
- `Sum` constructor disjointness: `Sum.inl_ne_inr`/`simp` closes the
  first-visit goals once states are projected.
