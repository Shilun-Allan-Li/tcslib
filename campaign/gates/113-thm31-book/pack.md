# External audit pack: the book-form time hierarchy (PR #223, a statement-and-proof gate)

## Why this PR

[AB09, Theorem 3.1] says that if `f, g` are time-constructible and `f(n) log f(n) = o(g(n))`,
then `DTIME(f) ⊊ DTIME(g)`. Until now the library proved it only with quadratic overhead:
`time_hierarchy`, needing `(f n + n + 1)² = o(g)` (`TimeHierarchy/Diagonal.lean`, Hydroxyi's
file). The parameterized argument (U2 Part 1, #100) reduces any hierarchy to a **self-simulator**
at some overhead. This PR supplies the `O(t log t)` self-simulator and states the book's form.

The self-simulator is U2-U, the self-application universal machine at two work tapes
(`exists_selfUniversalK 2`). Its normal form is `two_work_tapes_binary`, which rests on
`two_work_tapes_run` ([HS66]), proved by G5 in #211, now merged.

**Rulings:**
- 2026-10-14, all as recommended:
  - Q7: state both forms, with the book form under `∀ n, n ≤ f n` rather than
    `TimeConstructible f`;
  - Q8: the home is the end of `Diagonal.lean`, authorized;
  - Q10: no `DTIME(n+1) ⊊ DTIME((n+1)²)` illustration;
  - no U2-V;
  - the facade sentence is fixed here.
- 2026-11-06 (the user): land after #211, admission-free, **with `time_hierarchy_book_of_pos`**.

**The PR:** #223 on `lean/thm31-book`, head `05050b3d` (full hash in the bundle header). It
consists of the change `0a4520df`, the facade `1e92eaa9`, the docstring `a08d70d9`, and merges of
the campaign, the last after #218 and #219. It changes two files:
- `TimeHierarchy/Diagonal.lean`: 536 → 799 lines, 24 → 40 public, 0 → 1 private;
- the `TimeHierarchy` facade (one sentence).

## The statements (verify)

```lean
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hpos : ∀ n, 0 < g n) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g
```

**Reading against the book:**
- `f log f = o(g)` is read as "for every `A`, eventually `A · f n · log₂ f n ≤ g n`", the
  library's convention, as in `time_hierarchy`.
- `hf : n ≤ f n` replaces `TimeConstructible f` (Q7). Under it, `log₂ f n ≥ 1` once `n ≥ 2`, so
  the case `f n ≤ 1` (`Nat.log 2 (f n) = 0`) occurs only for `n ≤ 1`, which an eventual
  hypothesis never reaches. Without `hf` the statement would be false: at `f = 1`,
  `f log f = 0` and the hypothesis holds for every `g`. The docstring says so.
  `time_hierarchy_log` needs no hypothesis on `f`.
- `DTIME (g + 1)` is the library's form, as in `time_hierarchy`. `_of_pos` gives the book's
  literal `DTIME g` for positive `g`, mirroring `time_hierarchy_of_pos`.

## What changed (verify)

**New declarations** (all at the end of `Diagonal.lean`, namespace `Complexity.TimeHierarchy`
unless marked):
- `logOverhead t := (t + 1) * (Nat.log 2 (t + 1) + 1)` and `logDiagOverhead t n`, each with its
  `_eq`;
- the arithmetic: `le_logDiagOverhead`, `logOverhead_add_le`, `logOverhead_mul_le`,
  `logDiagOverhead_le_book`, and one private `eventually_logDiagOverhead_le`;
- `code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2`, with `_eq`;
- `twoTapeSelfSimulator : SelfSimulator logOverhead`, with `_W` and `_decode` (`rfl`):
  - **`simulates`:** `W := Classical.choose (exists_selfUniversalK 2 code₂.toK)`. The forward
    clause gives `C · (t + 1)` steps, lifted to `C · (t + |pairEncode α w| + 1)` by `.mono`,
    through `EffectiveMachineCode2.toK_toFinTM`.
  - **`normalForm`:** chains `two_work_tapes_binary`, then `exists_code2TM`, then `code₂.encode`
    with `MachineCode2.decode_encode`, then `logOverhead_mul_le`.
- in namespace `Complexity`: the three theorems. Each applies
  `(twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le)` with `le_logDiagOverhead`.
  The book forms pass the private helper's conclusion to `.time_hierarchy` or
  `.time_hierarchy_of_pos`.

**Unchanged:** every existing declaration of `Diagonal.lean`, byte-identical
(`evidence/freeze/`). The module docstring's opening, "Divergences", "Main definitions" and
"Main results" are rewritten. The facade's sentence "quadratic overhead in place of the book's
`f log f`" now names `time_hierarchy_book`.

**Imports:** `Robustness/TwoTapes` and `UniversalK` are added. Neither closure contains
`Diagonal`.

## Known deviations (for the audit)

- **Rule 10, two reads in `twoTapeSelfSimulator.normalForm`:**
  - `rintro ⟨c₀, M, hM⟩` destructures a `DTIME` membership;
  - `hM` is passed where `computesFunInTime_iff`'s right side is expected (`DecidesInTime`).

  Neither definition has a published characterization (no `mem_DTIME_iff`; no `FinTM`
  `decidesInTime_iff`). The received `oneTapeSelfSimulator` reads both the same way. The seal
  below isolates exactly these two. Publishing the two equations in `ClassP/DTIME` would replay
  most of the tree. It is recorded for the dedup window.
- **The lint's check 8** reads `code₂` and `code₂_eq` as `code`, because the identifier class is
  ASCII-only. `code₂_eq` exists.

## Brief for the auditor

1. **The statements:** are they the book's Theorem 3.1 under the conventions above? Check the
   boundary cases: `f n ≤ 1`, `g` vanishing (the `+ 1`), and the `Nat.log` floors.
2. **The proofs:**
   - Is `twoTapeSelfSimulator` a valid `SelfSimulator logOverhead`, in both its clauses?
   - Is the arithmetic right: `logOverhead_add_le` (`logOverhead t + n + 1 ≤ 2 · logDiagOverhead t n`),
     `logOverhead_mul_le`, and `logDiagOverhead_le_book` (`≤ 12 · f log f` for `2 ≤ n ≤ f`)?
3. **Rule 10:** are the two disclosed reads the only ones? Is the seal adequate?
4. **Duplication:** does anything re-derive a published lemma? The screen and gate 24's carried
   checks are below.
5. **Public text:** is it accurate, attributed, and free of campaign labels?

## Repository-side attestations (verify or challenge)

- **Axioms** (`evidence/probes/axioms.*`): `time_hierarchy_log`, `time_hierarchy_book`,
  `time_hierarchy_book_of_pos`, `twoTapeSelfSimulator` and `two_work_tapes_run` all use
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10** (`evidence/probes/seal.*`): three verbatim copies of the new section, each in its
  own namespace under `attribute [local irreducible]`:
  - **A** seals `DTIME`, `DecidesInTime`, `TimeConstructible`, `ComputesInTime`,
    `ComputesFunInTime`, `EffectiveCodeK.toFinTM`, `EffectiveMachineCode2.toK`,
    `Code2TM.toFinTM`, `indicator`, `toDiagSimulator` and `mono`;
  - **B** seals all but `DTIME`;
  - **C** seals all but `DTIME` and `DecidesInTime`.

  Each copy opens with `fail_if_success rfl` controls. The output has exactly two errors: A at
  the `DTIME` destructuring (line 170) and B at the `DecidesInTime` read (line 422). C
  elaborates.
- **Gate 24's carried sanity checks** (`evidence/probes/sanity.*`): all of the following
  elaborate with exit 0:
  - `¬ Nonempty (DiagSimulator (fun _ _ => 0))`;
  - `¬ Nonempty (SelfSimulator (fun _ => 0))`;
  - no `SelfSimulator` with a constant `decode`;
  - the `rfl` projections of `mono`/`toDiagSimulator` and of the new instance.
- **Freeze** (`evidence/freeze/`, the head against the campaign's Lean `7027dead`):
  - `Diagonal`: 24 → 40 public (the 16 above), 0 → 1 private. No existing declaration changed,
    and none was removed.
  - The facade: no declarations.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `TimeHierarchy` gives 0 FAIL, 4 WARN over 5 files, at both base and
    head.
  - The policy linter gives 3 findings at both, the facade's pre-existing missing `set_option`s.
- **Screen** (`evidence/screen/`, the `TimeHierarchy` population at base and head):
  - the head has 72 declarations, 23 pairs and 3,903 characters, against 62, 16 and 3,277 at
    the base;
  - 7 pairs are new, all between new declarations or with a short projection: the three
    theorem forms against each other, `logOverhead_add_le` against `le_logDiagOverhead`, and
    `twoTapeSelfSimulator_decode` against `diagLang_not_mem_DTIME`'s one line;
  - none pairs with `oneTapeSelfSimulator`.
- **Replay** (`evidence/merged-tree/`): `replay-lt32` at `05050b3d` covers `Diagonal`'s
  downstream closure (14 modules, now including `Hierarchy`), chained from the campaign snapshot
  after #218 and #219. **14 modules, 0 failed.** The static check finds 0 mismatches. The 2
  `sorry` warnings are `Hierarchy`'s F6 and E-PAD.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/113-thm31-book/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `thm31-book-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
