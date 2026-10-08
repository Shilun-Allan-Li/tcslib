# External audit pack — Chapter 4, phase P4.1 (space classes), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P4.1 —
the nondeterministic space measure, `NSPACE`, the classes
`PSPACE`/`NPSPACE`/`NL`/`coNL`, space-constructibility, Theorem 4.2's first two
inclusions, Example 4.6's memberships, and Example 4.7's parity language.
Statement phase per `workflow.md` §2-3; the gate closes on a round with zero
blockers and zero majors.

Audited at commit `edea2663` (branch `complexity/arora-barak-ch3-4`); the seven
files under audit are byte-identical to their landing commit `2cf44f1d` except
the facade's import/Contents additions. Under audit:
`TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean` and
`TCSlib/Complexity/SpaceComplexity/{NSPACE,SpaceClasses,Constructible,Inclusions,Examples}.lean`
plus the `SpaceComplexity.lean` facade additions — **14 sorried statements,
2 definitions of measure, 6 class/predicate definitions.**

**This phase sits directly on the P0-closed reception surface**
(`audits/ch34-p0-resolutions.md`): `Complexity.SPACE`, `LOGSPACE`,
`Turing.FinTM.ComputesInSpace`, `logSpace`, and the **positive-bound
convention** adopted there (one zero of a bound collapses `SPACE` to the
zero-work-tape class; every asymptotic chapter bound is everywhere positive —
`n + 1`, `n ^ c + 1`, `logSpace`). The `ZeroSpace.lean` sanity layer is attached
as closed context.

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **a space measure whose quantifier shape silently
under- or over-counts along nondeterministic branches**, and **a class
definition that re-opens the zero-bound collapse the P0 gate just closed**.
Blind restatements for every definition; true-as-stated arguments for every
sorried statement; at least **5 adversarial instantiations**; no blanket
approvals. Sources: [AB09] §4.1 (Definition 4.1, Remark 4.3, Theorem 4.2,
Definition 4.5, Examples 4.6-4.7, Figure 4.1) and §4.1's `S(n) > log n`
convention (p. 79).

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p41-sweep.log`, revision recorded at
  start): all seven modules, 0 `error:` lines, fresh `.olean`s, exactly **14**
  `declaration uses 'sorry'` warnings (NondeterministicSpace 2, NSPACE 2,
  SpaceClasses 3, Constructible 2, Inclusions 4, Examples 1).
* Style lint (`audits/logs/ch34-p31-p41-stylelint.log`): `SpaceComplexity`
  0 FAIL / 0 WARN over 35 files.
* Statement-freeze baseline: commit `edea2663`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **All branches halt** (`FinNDTM.DecidesInSpace`; maintainer decision
   CH34-Q7): deciding includes `Turing.NDTM.HaltsWithin` at an existential
   per-input budget `T`. [AB09, Remark 4.3] calls the restriction harmless for
   space-constructible bounds; the campaign adopts it outright, matching
   `NTIME`'s totality convention.
2. **Visited cells for both classes**: [AB09, Def 4.1]'s own wording counts
   visited locations for `SPACE` but nonblank for `NSPACE`; the campaign uses
   visited for both (documented at the definition site since P0). The branch
   measure `Turing.NDTM.spaceUsedWith` mirrors the deterministic
   `visitedByTapeHead` along `runWith` prefixes.
3. **Exact-length choice words**: the space condition quantifies over words of
   length exactly `T`; sufficiency is pinned by the (sorried) invariance
   statement `spaceUsedWith_append_of_halt` — all-branch halting at `T`
   freezes every branch's space. The definition stands alone; the lemma
   documents why the quantifier shape loses nothing.
4. **The zero-bound collapse is inherited, knowingly**: `spaceUsedWith` also
   dominates the tape count (every tape's visited set contains its origin),
   so `NSPACE s` with a zero of `s` collapses exactly as `SPACE s` does. The
   phase's own classes are positive-normalized (`n ^ c + 1`, `logSpace`); no
   `NSPACE`-side `ZeroSpace` twin is stated in this skeleton — **seeded
   question 2 asks whether the gate should demand one**.
5. **`SpaceConstructible` carries the book's convention as data**:
   `(∀ n, logSpace n ≤ S n) ∧ ∃ c > 0, ∃ M, ComputesInSpace (bits ∘ S ∘ length)
   (c · S)` — mirroring `TimeConstructible` (binary output, constant slack);
   results needing only weaker hypotheses must say so. Instances stated:
   `logSpace` and `fun n => n + 1`.
6. **`DecidesInSpace`'s time is an existential per input** (inherited from the
   received `ComputesInSpace`): the P0 round-2 auditor already judged this the
   right shape ("no uniform-time existential has to be added"); the
   configuration-count layer recovers time from space when needed.
7. **Deferred, recorded in the plan**: `MULT` (Ex 4.7's second language) to
   P4.4 with the encoding conventions; the nondeterministic and
   polynomial-width ARM extensions to the §12 gate + colleague sync; Theorem
   4.2(iii) and Savitch to P4.2 (configuration graphs).
8. **`evenLang`** is `{x | x.count true % 2 = 0}`; its `LOGSPACE` membership
   statement predates the P0 round-2 addition of the *zero-tape* witnesses in
   `ZeroSpace.lean` — at fill time the membership should flow from
   `evenLang_mem_SPACE_zero` by monotonicity, and the `Examples.lean` sketch's
   one-work-tape machine is superseded (seeded as a harmonization note, not a
   statement change).
9. **`DTIME_subset_SPACE`** handles vanishing time bounds by the established
   emptiness convention (`DTIME` with a zero is empty — no machine halts in
   zero steps from a live initial state); the sketch names the absorbed
   constant `k · c + k`.

## Specific questions (prioritized)

1. **The branch space measure** (`visitedWith`/`spaceUsedWith`): blind-restate
   and check the prefix indexing (`Finset.range (w.length + 1)`, prefixes via
   `w.take j`) — are the endpoints right (initial head counted; the position
   after the full word counted; nothing beyond)? Is per-branch counting (one
   word at a time, no union over branches) the faithful reading of [AB09,
   Def 4.1]'s "regardless of its nondeterministic choices"?
2. **`DecidesInSpace`/`NSPACE` shape**: does the existential budget `T`
   together with exact-length quantifiers deliver Definition 4.1 + Remark
   4.3, or can an adversarial machine exploit the shape (e.g. huge `T` with
   accepting branches halting early and *late* branches visiting more —
   covered by all-branch halting at `T`?)? Should the gate demand the
   `NSPACE` zero-bound sanity twin (deviation 4), or does the P0-closed
   convention suffice?
3. **`SpaceConstructible`** (deviation 5): is bundling `logSpace n ≤ S n`
   faithful to p. 79's `S(n) > log n` (note `logSpace = ⌊log₂ n⌋ + 1` — check
   the off-by-one against the book's strict inequality at small `n`), and are
   the two instance statements true as stated (in particular
   `logSpace n ≤ n + 1` at `n = 0`)?
4. **Theorem 4.2(i)/(ii) statements** (`DTIME_subset_SPACE`,
   `SPACE_subset_NSPACE`): check the constant-absorption arithmetic
   (`k · (c·T + 1) ≤ (k·c + k) · T` needs `T ≥ 1` — is the vacuity route at
   zeros airtight given `DTIME`'s own convention?), and the measure-transfer
   sketch for (ii) (`toNDTM_spaceUsedWith`, sorried in this same phase — is
   the dependency ordering of the two sorried statements sound?).
5. **Example 4.6's statements** (`NP_subset_PSPACE`, `SAT3_mem_PSPACE`): is
   the class-level statement the book's, and is the certificate-cycling
   sketch's space ledger (certificate tape + re-executed verifier through
   `DTIME_subset_SPACE` + counter) complete, or does it hide a
   composition-with-space obligation this phase cannot discharge (the §12
   space clauses are a concurrent gate — flag any hard dependency)?
6. **Class definitions** (`PSPACE`, `NPSPACE`, `NL`, `coNL`,
   `LOGSPACE_subset_NL`, `PSPACE_subset_NPSPACE`): any daylight against
   [AB09, Definition 4.5] and §4.3.2, given the positive normal forms and the
   received `logSpace` floor?
7. **Adversarial instantiations to attempt**: `s = 0` through `NSPACE` (the
   collapse, deviation 4); a machine whose branches halt at different times
   under one `T`; `w = []` in the branch measure; `NL` at inputs of length
   `0`/`1`; `SpaceConstructible (fun n => n + 1)` at `n = 0`; `coNL` of the
   empty and full languages.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p41-findings.md`; the gate closes on zero blockers and majors.
