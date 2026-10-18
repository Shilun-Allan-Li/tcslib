# Ch3–4 fill campaign — Epoch C1, Batch C1a: nondeterministic space and the easy space inclusions

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD`
  succeeds. That commit lands the two shared lemmas this brief cites
  (below) and the order list. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/ch34-c1a`). Record the base commit hash in `REPORT.md`. Never
  rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch34-c1a.zip`, containing `REPORT.md`, the full modified sources, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **nine audited-true statements** of chapter 4's space-class layer
(phase P4.1) that epoch C1 assigns to this batch (plan §4e):

- the two run lemmas of the nondeterministic space measure;
- `NSPACE` monotonicity and `SPACE ⊆ NSPACE`;
- the three definitional class inclusions;
- `DTIME ⊆ SPACE` ([AB09, Theorem 4.2], first inclusion) and `P ⊆ PSPACE`.

None needs a machine construction. They are run-level prefix arguments, a
cardinality bound, and union bookkeeping. The P4.1 statement gate passed in
one round (0 blockers, 0 majors). Read in full:

- `audits/ch4-p41-findings.md`: its statement-by-statement rows 1–7 and
  10–11, and its answers Q1, Q2 and Q4, are your **binding routes**;
- `audits/ch4-p41-resolutions.md`;
- `policy.md`, `workflow.md` §4, and plan §4e (the partition and the
  citation rule).

Batches **C1b**, **C1c**, **C1d** and the summit batch **S1** run
concurrently on disjoint files.

**Two shared lemmas were landed for you** at the issue commit, so that this
batch cites rather than copies:

- `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`TuringMachine/Finite.lean`):
  `tm.spaceUsed cfg t ≤ k * (t + 1)`. It is the bound `DTIME_subset_SPACE`
  needs. Catalog's private `f2_space_of_time` proves a variant of it; that
  copy is 12.2c's to remove, not yours.
- `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff`
  (`ClassNP/NTIME.lean`): if `M` computes `[x ∈ L]` by time `t`, then
  `M.toFinNDTM.tm.HaltsWithin x t ∧ (x ∈ L ↔ M.toFinNDTM.AcceptsWithin x t)`.
  It is the per-input content of `Complexity.DTIME_subset_NTIME`, which now
  cites it.

**Pre-ship check (maintainer, executed):**
`audits/evidence/ch34-c1/C1aPreShip.lean.txt`, with output `C1aPreShip.out`.
The call shapes of routes 2, 4 and 8 elaborate against the frozen
statements, and both shared lemmas print within the standard triple.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/NondeterministicSpace.lean:89` | `Turing.NDTM.spaceUsedWith_append_of_halt` | per-tape visited-set **equality**; the short-prefix inclusion as its own lemma | — |
| 2 | `TuringMachine/NondeterministicSpace.lean:107` | `Turing.MultiTapeTM.toNDTM_spaceUsedWith` | pointwise image agreement on `range (w.length + 1)` | — |
| 3 | `SpaceComplexity/NSPACE.lean:103` | `Complexity.NSPACE.mono` | same witness, space conjunct weakened | — |
| 4 | `SpaceComplexity/NSPACE.lean:117` | `Complexity.SPACE_subset_NSPACE` | `M.toFinNDTM` at the per-input halting time | 2 |
| 5 | `SpaceComplexity/SpaceClasses.lean:69` | `Complexity.space_poly_subset_PSPACE` | `Set.subset_iUnion` | — |
| 6 | `SpaceComplexity/SpaceClasses.lean:76` | `Complexity.PSPACE_subset_NPSPACE` | `Set.iUnion_mono` over 4 | 4 |
| 7 | `SpaceComplexity/SpaceClasses.lean:83` | `Complexity.LOGSPACE_subset_NL` | 4 at `logSpace` | 4 |
| 8 | `SpaceComplexity/Inclusions.lean:55` | `Complexity.DTIME_subset_SPACE` | the shared space bound; vacuity at a zero | — |
| 9 | `SpaceComplexity/Inclusions.lean:63` | `Complexity.P_subset_PSPACE` | `Set.iUnion_mono` over 8 | 8 |

Fill in the import order: `NondeterministicSpace`, `NSPACE`,
`SpaceClasses`, `Inclusions`.

**`Inclusions.lean` is shared.** You own the whole file for the epoch but
change only the bodies of targets 8 and 9, plus new `private` helpers above
them. `NP_subset_PSPACE` and `SAT3_mem_PSPACE` (group B2, a later epoch)
stay byte-identical.

### Proof routes (binding; the audit's derivations, amplified)

1. **`spaceUsedWith_append_of_halt`.** For every tape `i`, prove
   `tm.visitedWith (w ++ w') cfg i = tm.visitedWith w cfg i`. This is an
   **equality of visited sets, not an inequality of totals** (audit Q1).
   Then sum.
   - **⊇, with no halting hypothesis** (the short-prefix argument, note 7):
     for `j ≤ |w|`, `(w ++ w').take j = w.take j`. State this inclusion as
     **its own `private` lemma**, and record the short-prefix argument as a
     flagged docstring sketch appendix on target 1. The P4.1 resolutions
     carry it into this fill, because post-halt invariance alone explains
     only longer words.
   - **⊆, using `h`:** for `|w| < j`,
     `(w ++ w').take j = w ++ w'.take (j - |w|)`.
     `Turing.NDTM.runWith_append` factors the run through
     `tm.runWith w cfg`, and `Turing.NDTM.runWith_of_halt _ h` absorbs the
     rest, so the position is the one at `j = |w|`.
   - `Finset.image_congr` does **not** apply (the domains differ). Use
     `Finset.ext` or `Finset.Subset.antisymm` with `Finset.mem_image`.
2. **`toNDTM_spaceUsedWith`.** Both sides are sums over `Fin k` of
   cardinalities of images of `Finset.range (|w| + 1)`. Per tape, use
   `Finset.image_congr`: for `j` in the range,
   `Turing.MultiTapeTM.toNDTM_runWith (w.take j) cfg` and
   `List.length_take_of_le` give
   `tm.toNDTM.runWith (w.take j) cfg = tm.runFrom cfg j`.
3. **`NSPACE.mono`.** Reuse the constant, machine and per-input budget `T`.
   Only the space conjunct changes:
   `(hsp w hw).trans (Nat.mul_le_mul_left c (h _))`. This holds at `c = 0`.
4. **`SPACE_subset_NSPACE`** (audit Q4). Take the same constant `c` and the
   witness `M.toFinNDTM`. On input `x`, `Turing.FinTM.DecidesInSpace` gives a
   time `t` with `M.ComputesInTime x [indicator] t` and the space bound.
   Take `T := t`:
   - halting and acceptance are **both** given by
     `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff` applied to that
     computation. **Cite it; do not re-derive them.**
   - the branch space of any length-`t` word is `M`'s space at time `t`, by
     **target 2**.

   Do not route through target 1 or constructibility (Q4: neither is
   needed).
5. **`space_poly_subset_PSPACE`.**
   `Set.subset_iUnion (fun c : ℕ => SPACE fun n => n ^ c + 1) c`, as in
   `Complexity.dtime_poly_subset_P`. Degree zero is included.
6. **`PSPACE_subset_NPSPACE`.** `Set.iUnion_mono fun c =>
   SPACE_subset_NSPACE _`.
7. **`LOGSPACE_subset_NL`.** `SPACE_subset_NSPACE logSpace`.
8. **`DTIME_subset_SPACE`** (audit row 10 and Q4).
   - **Vacuous case:** if `∃ n, T n = 0`, then `DTIME T = ∅` by the proved
     `Complexity.DTIME_eq_empty_of_exists_zero`. Cite it.
   - **Positive case** (`1 ≤ T n` for all `n`): the witness is `M` itself,
     with constant `M.k * c + M.k`, and the time `c * T |x|` instantiates
     `ComputesInSpace`'s existential (the `ComputesInTime` is `hM x`
     verbatim). The space bound is
     `Turing.MultiTapeTM.spaceUsed_le_mul_succ` at `c * T |x|`, followed by
     `k (cT + 1) = kcT + k ≤ kcT + kT = (kc + k) T`.
9. **`P_subset_PSPACE`.** `Set.iUnion_mono fun c => DTIME_subset_SPACE _`,
   across the identical normal forms `n ^ c + 1` of `Complexity.P` and
   `Complexity.PSPACE`.

## Cited infrastructure (public and proved at the issue commit)

- `TuringMachine/Nondeterministic.lean`:
  - `Turing.NDTM.runWith_append`, `runWith_of_halt`, `runWith_cons`,
    `runWith_nil` and `stepWith_of_halt` (target 1);
  - `Turing.MultiTapeTM.toNDTM_runWith` and `Turing.FinTM.toFinNDTM`
    (targets 2 and 4).
- `TuringMachine/Deterministic.lean` (vendored; never edit): `visitedByTapeHead`,
  `spaceUsedByTape`, `spaceUsed`, `runFrom_add`, `runFrom_of_halt`,
  `indicator`.
- `TuringMachine/Finite.lean`: `Turing.FinTM.computesInTime_iff` and
  **`Turing.MultiTapeTM.spaceUsed_le_mul_succ`** (target 8).
- `ClassNP/NTIME.lean`: **`Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff`**
  and `Turing.FinNDTM.AcceptsWithin` (target 4).
- `SpaceComplexity/Basic.lean`: `Turing.FinTM.ComputesInSpace`,
  `DecidesInSpace`, `Complexity.SPACE` and `logSpace`.
- `ClassP/DTIME.lean`: `Complexity.DTIME_eq_empty_of_exists_zero` (target 8).

Every module upstream of your files is sorry-free, so the **"proved modulo"
set is empty**. A complete delivery has no `sorryAx`. Downstream, C1d's
`PSPACE_eq_P_of_pspaceComplete_mem_P` is proved modulo your
`P_subset_PSPACE`; nothing for you to do. **Do not cite**
`Turing.FinTM.k_le_spaceUsed` (`ZeroSpace.lean`, sorried, batch C1b) or
anything in `ConfigGraph.lean` (S1).

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p41-findings.md`, the **statement-by-statement
disposition**:

> | 1 | `NDTM.spaceUsedWith_append_of_halt` | Prefixes through \(|w|\) are unchanged; every later prefix runs from the halted configuration reached by \(w\), so its position is already in the old visited set. Equality holds tape by tape, hence after summation. No finiteness of raw states or symbols is needed. |
> | 2 | `MultiTapeTM.toNDTM_spaceUsedWith` | For every \(j\le |w|\), the embedded run under \(w.take\,j\) is the deterministic run for \(j\) steps. Both finite images have exactly the domain \(0,\ldots,|w|\). Their cardinality sums agree. |
> | 4 | `SPACE_subset_NSPACE` | Embed the deterministic witness, preserving tape count and configurations. Use its per-input halting budget. Every choice word reproduces its output and space; a word of that length always exists. See question 4. |
> | 10 | `DTIME_subset_SPACE` | A length-\(cT(n)\) run visits at most \(k(cT(n)+1)\) cells. Absorb the initial \(k\) cells using positivity; if the bound has a zero, DTIME is empty. See question 4. |

From **Q1** (target 1):

> Thus \(j=0\) counts the initial position and \(j=|w|\) counts the final position, including a move executed by the halting transition. There is no \(j=|w|+1\) term.

From **finding 7** and **Q2** (the short-prefix argument):

> - If \(|u|\le T\), set \(v=u++[false]^{T-|u|}\). Then \(|v|=T\), and every prefix position of \(u\) occurs among those of \(v\).

From **Q4** (targets 4 and 8):

> For the deterministic-to-nondeterministic transfer, choose the same constant and `M.toFinNDTM`. On each input take the time supplied by `M.DecidesInSpace`. Every length-\(T\) word gives the identical deterministic configuration and the identical visited-cell sum. If the input is a member, \([false]^T\) supplies an accepting word; if it is not, all words give \([false]\), so none accepts.

> The dependency direction is sound:
> `toNDTM_runWith` → `toNDTM_spaceUsedWith` → `SPACE_subset_NSPACE` → class inclusions.

Finding 8 and Q5 (the host obligations of `NP_subset_PSPACE`) belong to the
B2 brief. Note 6's local `NSPACE` documentation is already in place.

## Ground rules (binding)

1. **File ownership.** Only the four owned files. In them, only the nine
   targets' bodies plus new `private` helpers. List every new declaration
   with its role; the epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements or
   attribution edits. Docstrings stay. Flagged sketch appendices are
   allowed. **Module-docstring status lines** that call a target sorried
   (for example "Main results (sorried; phase-P4.1 statements)") may be
   updated to say it is proved, and nothing else in a module docstring may
   change. Flag each such update.
3. **Escalation** on anything unprovable as stated: stop on that item,
   record the obstruction, and continue with the rest.
4. **No touching other sorries**, `NP_subset_PSPACE` and `SAT3_mem_PSPACE`
   included.
5. **Cite, never re-prove, proved material**, in particular the two shared
   lemmas above.
6. **Imports unchanged.** Every cited declaration is reachable now. A
   Mathlib import is allowed only if a needed lemma requires it; flag it.
   No TCSlib import may be added; escalate instead.
7. **One proof per shared argument.** The short-prefix inclusion of target 1
   is one lemma.
8. **Requested shared lemmas**: none expected. If one arises, use a
   `private` local copy and list it.
9. **Continuation budget.** If your budget runs out, deliver a partial zip
   whose `REPORT.md` states:
   - which targets are proved;
   - which `private` helpers remain `sorry` (allowed only in a partial
     delivery, each with a "Proof sketch");
   - which proved targets are then proved modulo one of yours.

## Duplication governance (binding)

Run the text-level screen **before and after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean \
  TCSlib/Complexity/SpaceComplexity/NSPACE.lean \
  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean \
  TCSlib/Complexity/TuringMachine/Nondeterministic.lean \
  TCSlib/Complexity/ClassNP/NTIME.lean \
  TCSlib/Complexity/SpaceComplexity/Basic.lean \
  TCSlib/Complexity/ClassP/DTIME.lean \
  TCSlib/Complexity/TuringMachine/Finite.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean
```

- **No new cross-file pair.** No pair present after but not before may have
  an owned-file declaration on one side and another file's on the other.
- The shared lemmas remove the two known hazards: `DTIME_subset_NTIME`'s old
  body, and Catalog's `f2_space_of_time`. `SPACE.mono` (about 73
  characters) and `NTIME.mono` and `HaltsWithin.mono` are short, so a
  near-verbatim target 3 can still pair. Write each proof from its route.
  If a pair appears anyway, report it with both declarations and the shared
  fraction; never ship it silently.
- List every new in-file pair with a one-line justification. A pair at 90%
  or more is a copy; factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**,
  with each proof's citations named.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-c1a.txt`. It lists, in
  dependency order, the upstream closure of your files **and** of every
  module downstream of them:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-c1a.txt )
  ```

  Record the base sorry-warning set before editing.
- Iterate per edit on the changed file, then the later owned modules in
  order.
- **Final checks:**
  1. **Owned modules:** zero errors and zero sorry warnings, except exactly
     two in `Inclusions.lean`, at `NP_subset_PSPACE` and `SAT3_mem_PSPACE`.
  2. **Every downstream module**, the `SpaceComplexity` and `ClassPSPACE`
     facades included: zero errors, and sorry warnings exactly the base's.
     These are `ConfigGraph`, `ClassPSPACE/TQBF`, `Savitch`, `Hierarchy`
     and `Logspace/{Reductions,Path,ImmermanSzelepcsenyi}`. The root
     `TCSlib` module is excluded.
- **Axiom prints** for all nine targets: at most
  `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py` on
  `TCSlib/Complexity/TuringMachine` and on `TCSlib/Complexity/SpaceComplexity`,
  0 FAIL each.

## Out-of-scope sorries you will see (leave every one untouched)

- **In your files:** `Complexity.NP_subset_PSPACE` and
  `Complexity.SAT3_mem_PSPACE` (`Inclusions.lean`), group B2.
- **Concurrent batches:**
  - **C1b:** `ZeroSpace`, `Examples`, `CounterProgRun`;
  - **C1c:** `OracleAgreement`, `OracleNondeterministic`,
    `ClassOracle/Classes`;
  - **C1d:** `Formulas/QBF`, `Formulas/QBFEncoding`, `ClassPSPACE/Games`,
    `ClassPSPACE/TQBF`, `Logspace/Reductions`,
    `Diagonalization/Relativization`;
  - **S1:** `ConfigGraph`.
- **Every other chapter-3/4 statement surface.**

If a proof seems to *need* one of these, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 9/9, or the partial frontier (rule 9); the base hash and the ancestor
      check.
- [ ] Every new declaration with its role; the short-prefix lemma
      identified.
- [ ] Imports added, or "none"; requested shared lemmas, or "none";
      docstring appendices and status-line updates, each flagged.
- [ ] Escalations, or "none".
- [ ] Duplication: the screen before and after, every new in-file pair
      justified, and "new copies: none".
- [ ] Final sweep tail (owned modules, then downstream with the facades),
      the nine axiom prints, and the two lint lines.
- [ ] Diff touches only the four owned files.

## Known pitfalls at this pin (hard-won)

- **Visited-set indexing.** `visitedWith` and `visitedByTapeHead` range over
  `Finset.range (n + 1)`. `j = 0` is the start, `j = n` the final position
  (including a halting move's), and there is no `j = n + 1`.
- `List.length_take` returns `min`; use `List.length_take_of_le`. Use
  `List.take_append`, not the deprecated `take_append_eq_append_take`.
- Use the `notMem` spellings (`Set.eq_empty_iff_forall_notMem`); the
  `not_mem` names are deprecated.
- `MultiTapeTM.initCfg` and `NDTM.initCfg` are `@[simp] def`s. Bare `simp`
  unfolds them to `Cfg.init` and breaks folded forms; prefer `simp only`.
- `M.toFinNDTM.tm` is `M.tm.toNDTM` only definitionally. If `rw` fails to
  match, state the specialized equation with an explicit type, or use
  `show`/`change` first.
- `Turing.FinTM.DecidesInSpace` and `Turing.FinNDTM.DecidesInSpace` share a
  short name. Dot notation resolves by type, but `unfold`/`simp only` need
  the qualified name. `SPACE`'s bound arrives as
  `(fun n => c * s n) x.length`; beta-reduce before `omega`.
- `MultiTapeTM.indicator` is defined under `open Classical`: start with
  `classical`.
- `PSPACE`, `NPSPACE`, `NL`, `LOGSPACE` and `P` are `def`s, not `abbrev`s.
  `exact` sees through them, but `rw` may not; `unfold` or `show` the `⋃`
  form first.
- `Nat.mul_le_mul_left (k) (h : n ≤ m) : k * n ≤ k * m` takes the factor
  explicitly. `omega` cannot see through `Finset.card` or sums.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
