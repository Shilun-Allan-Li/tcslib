# §13 fill campaign — Tranche A-S2, Batch ZF-A: the zoned carrier (`Build/Zone.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-A`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `8f13d74ecba8e73a3642d605f462774092d7ef8a`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `zone-f1-A.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **20 audited-true sorried declarations** of
`TCSlib/Complexity/TuringMachine/Build/Zone.lean` (647 lines; the
authoritative inventory is the round-3 audit's: 16 sorried theorems plus
4 sorried definitions carrying 8 capacity-proof holes, 24 `sorry` terms in
all). The statement gate closed after a **three-round** audit
(`audits/zone-infra-{,r2-,r3-}findings.md`, loop summary
`audits/zone-infra-resolutions.md` — read all four). The auditors supplied
complete mathematical arguments for every statement; the key ones are
quoted below verbatim and are **binding proof routes**. Batches ZF-B
(`Codes2Tape.lean`) and ZF-C (the Robustness Z4 statements) run
concurrently — you never touch those files.

## Owned file (modify this and nothing else)

`Build/Zone.lean`, all 20 targets. Suggested order (pure before machine):

1. the 8 capacity fields of `zoneShiftIn`, `zoneShiftOut`,
   `zoneMoveRight`, `zoneMoveLeft` (the round-2 audit's direct arguments,
   quoted below);
2. `zoneCellOf_bits` is proved; `zoneIndex_eq_iff`, `zoneTape_empty`,
   `zoneTape_blank_outside`, `zoneTape_homeWrite` (layout arithmetic);
3. `zoneSide_shiftInW`, `zoneSide_shiftOutW`, `zoneShiftInW_full_donor`,
   `zoneSide_moveRight` (list identities);
4. `zoneCascade_cost_le` (pure arithmetic);
5. `zoneSide_cascadeRight`, `zoneCascadeRight_lengths`,
   `zoneCascadeRight_zero`, `zoneCascadeRight_blocked` (the cascade — the
   round-3 inductions below are the routes);
6. `spaceUsedByTape_le_card_Icc`;
7. **the two machine rows** `FinTM.exists_zoneShiftInTM` /
   `exists_zoneShiftOutTM` — the only machine construction of the batch
   and its summit; the round-1 implementation notes below are binding.

## Ground rules (binding)

1. **File ownership**: only `Build/Zone.lean`; only the 20 targets'
   proofs plus `private` helpers; list every new declaration.
2. **Statement freeze**: no renames, re-signatures, restatements, or
   attribution edits. Docstring sketch appendices allowed, flagged.
3. **Duplication governance** (`policy.md`, **Duplication**): zero new
   copies; `REPORT.md` carries the ledger line. The shift machines are
   **assembled from the §12 layer** (R3 transfers/clears via R2 seams)
   per the construction-reuse policy — cite, never re-derive.
4. **Escalation** on anything unprovable as stated: stop, record, deliver
   what exists.
5. **Continuation budget**: on exhaustion deliver a partial zip per the
   standard rule (sorried `private` helpers allowed only then, listed).
   The pure targets (1-6) are the cheap majority; prefer completing all of
   them plus one row over partial work on both rows.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`;
  **never `lake build`**.
- Bootstrap: the 65-module order list, then `Build/Embed`, `Build/Seam`,
  `Build/Catalog`, `Build/VirtualInput`, `Build/Zone` (known baseline
  admissions are out of scope: `CounterProgRun` S9, the chapter-3/4
  statement surfaces, `Codes2Tape`, the Robustness Z4 rows).
- Iterate per edit on your file. Final:
  `Build/Zone` with **zero errors and zero sorry warnings**, then the
  `TuringMachine` facade (zero errors).
- **Axiom prints** for all 20 filled declarations: at most
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  — 0 FAIL.

## Inherited audit contracts (verbatim; binding)

**Layout arithmetic** (round-2 findings): write `s = 2r + ε`; both base
endpoints are even, so

> `2(2^i−1) ≤ 2r+ε < 2(2^{i+1}−1) ⟺ 2^i−1 ≤ r < 2^{i+1}−1 ⟺ 2^i ≤ r+1 <
> 2^{i+1} ⟺ ⌊log₂(r+1)⌋ = i`. Here `r+1 ≥ 1`, so there is no
> logarithm-at-zero case.

Small-`s` regression table: slots 0-1 → 0, 2-5 → 1, 6-13 → 2, 14-29 → 3.
Extent: the last slot is `zoneBase ℓ − 1`, giving the sharper interval
`[−2·zoneBase ℓ, 2·zoneBase ℓ + 1]` inside the stated symmetric bound; at
`ℓ = 0` only home cells 0/1 are nonblank. Cell parity: right slot `s` ↦
`n = 2s` presence / `2s+1` data; left ↦ `n = 2s+1` presence / `2s` data.

**Capacity fields** (round-2/round-3): inward lower prefix has length at
most `2^(i−1) ≤ zoneCapacity (i−1)` and the donor's suffix cannot grow;
an enabled outward guard makes the moved suffix exactly `2^(i−1)` and its
room conjunct bounds the new upper word; disabled guards change nothing;
the pushed head-move word's extra cell is covered by its room hypothesis
and a tail never grows; untouched levels keep their bounds.

**List identities** (round-2): enabled inward replaces the adjacent
segment `[] ++ wᵢ` by `take q wᵢ ++ drop q wᵢ`; enabled outward
reassociates `take q wᵢ₋₁ ++ (drop q wᵢ₋₁ ++ wᵢ)`; disabled guards are
identities; the full-donor theorem follows by unfolding the two enabled
inward branches, using `i − 1 ≠ i` when `1 ≤ i`.

**The cascade word theorem** (round-3, the binding route):

> For `j = 0`: both folds are empty; natural subtraction gives the room
> premise exactly `|L₀| + 1 ≤ 2`; the guarded move fires; nonempty `R₀`
> makes taking the tail of the whole right concatenation remove exactly
> its first cell. For `j ≥ 1`: on the left descent, stage `j`'s guard is
> exactly the room premise, and before each stage `i < j` the receiving
> word has length `2^i` against a full level `i−1`, legal because
> `2^i + 2^(i−1) = 3·2^(i−1) ≤ 4·2^(i−1)`. On the right descent each
> delivered word has length `min(|R_j|, 2^(i−1)) ≥ 1`. The single central
> move has the two required word effects, and every surrounding shift
> preserves the concatenations whether its guard fires or not. Half-full
> restoration is NOT used.

**The cascade lengths theorem** (round-3, the binding route): after the
descent, level 0 is `(1,1)` (right, left), levels `1 ≤ k < j` are
`(2^(k−1), 3·2^(k−1))`, the top is shifted by `2^(j−1)`; the move makes
level zero `(0,2)`; the ascent re-fires every guard —

> before stage `i`: level `i−1 = (0, 2^i)`; for `i < j`, level
> `i = (2^(i−1), 3·2^(i−1))` and `3·2^(i−1) + 2^(i−1) = 2^(i+1) =
> zoneCapacity i`; after stage `i`: level `i−1 = (2^(i−1), 2^(i−1))`,
> level `i = (0, 2^(i+1))`. At `i = j` the remaining donor has at least
> `2^(j−1)` cells and the second top push is legal exactly because
> `|L_j| + 2^(j−1) + 2^(j−1) = |L_j| + 2^j ≤ zoneCapacity j`.

**The blocked regression** (round-3): at every scheduled level the
receiving left word is still full, so `zoneCapacity i + 2^(i−1) ≤
zoneCapacity i` is false; inductively all left words are unchanged; full
level zero blocks the move; right shifts preserve their concatenation —
for arbitrary right data, including an empty right side.

**The cost lemma** (round-3): reindex to `4·Σ_{i=1}^{j}(2^i + i + 1) ≤
8·Σ 2^i = 16(2^j − 1) ≤ 16·2^j`, with `i + 1 ≤ 2^i` by induction from
equality at `i = 1` and `i + 2 ≤ 2(i+1) ≤ 2^(i+1)`; empty sum at `j = 0`.

**The machine rows** (round-1/round-3, binding implementation notes):

> The level is an input to one fixed machine, not a finite-control
> parameter. A direct implementation tests the lower guard, stages the
> affected words on tape 1, and rewrites the two adjacent windows. Word
> ends are distinguishable because a stored virtual blank occupies two
> nonblank false cells. Staging may copy the whole two-zone window; its
> size is still `O(2^i)`. A false guard returns the original tape and
> scratch word unchanged. Navigation counters and boundaries must be
> implemented with a geometric total ledger, rather than performing an
> `i`-cell counter scan for every cell moved — counting down a binary
> power of two with its least significant bit anchored has total
> carry/borrow work `Σ_{r=1}^{2^i}(1 + v₂(r)) < 2^(i+1)`; initializing
> the counter from unary `i` costs a polynomial in `i`, absorbed by
> `O(2^i)`. Bounded staging can use reserved invalid pair codes as
> temporary delimiters, saving overwritten boundary pairs in finite
> control and restoring them. The affected data window lies in
> `[−2·zoneBase(i+1), 2·zoneBase(i+1)+1]`, inside the row's interval;
> scratch is bounded separately. Every finite pass has a bounded stopping
> condition; cleanup restores the unary level and both heads; choosing
> the first halt time supplies the no-earlier-halt clause, positive
> because the initial state is live.

## Optional permanent lemmas (audit-adopted; deliver any subset, flagged)

Fixed-`ℓ` injectivity of `zoneTape` (never over unknown `ℓ` — empty outer
zones are invisible); `zoneSide` length arithmetic (`≤ zoneBase ℓ`);
direct slot readout at `zoneBase i + offset`; the small-`s` index table;
the sharper signed extent; guard-false identity specializations; home
readout for both moves; the mirrored `zoneSide_moveLeft`; an all-empty
blank-extension lemma.

## REPORT.md checklist

- [ ] 20/20 filled (or the partial frontier); base hash; new privates
      listed; optional exports listed or "none".
- [ ] Duplication ledger: "new copies: none"; the rows' §12 citations
      named (which R2/R3 facilities each phase consumes).
- [ ] Final sweep tail + 20 axiom prints + lint line.
- [ ] Diff touches only `Build/Zone.lean`.

## Known pitfalls at this pin (hard-won)

- `Nat.log2` characterization: work through `Nat.log2_eq_iff`-style facts
  or prove the sandwich by induction; `omega` cannot see `2^i` — feed it
  `Nat.two_pow_pos` and `pow_succ` rewrites first.
- `Finset.Icc` on ℤ is available (the cardinality lemma's `Int.card_Icc`);
  `Finset.Icc` on ℕ is NOT in this import closure — the cost lemma is
  already stated over `Finset.range` for that reason.
- `Fin.addCases`/`Fin.cases` after `by_cases` on `j.val`: `dsimp only`
  before rewriting; `Function.update_of_ne` (not `update_noteq`); avoid
  bare `simp` with folded forms.
- The guarded ops nest `dite`/`ite`: `split_ifs` early, then close each
  branch; the `by omega` proofs inside the guards are part of the term —
  use `zoneShiftInW`'s equation lemmas rather than unfolding by hand.
- For the rows, seam the phases with `seamCompTM`/`seamCompTM_run_ofCfg`
  (general-configuration forms — the zoned tape is not `Cfg.ofWords`) and
  the R3 transfer/clear rows via the R1 returning embeddings; the
  `bufferTape` level word on tape 1 behaves exactly as in the §12 loop
  host's fuel discipline (`f2_loopHost_fuel_*` are the proved precedent —
  cite the public exports, do not copy privates).
