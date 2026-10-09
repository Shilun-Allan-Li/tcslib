# External audit pack — Chapter 3, phase P3.3, round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P3.3, round 2. Round 1 (`audits/ch3-p33-findings.md`, attached verbatim)
returned **0 blockers, 2 majors, 7 minors, 2 notes** — both majors in
`ntime_hierarchy`'s proof sketch (the per-code universal constant cannot be
absorbed by choosing a padded large index, and the stage locator as
sketched was not computable within the allowance); no literal statement was
refuted. This round audits the repairs. The gate closes on zero blockers
and zero majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch3-p33-r2-repairs.diff`): **every theorem and definition
is unchanged**; the repairs are the rebuilt `ntime_hierarchy` sketch and
six sketch/docstring corrections. The inventory is unchanged (**7 sorried
statements, 7 definitions, 1 skeleton-time proof**).

## Brief for the auditor

You have the round-1 report. Your deliverables:

1. **For the two majors**: work the rebuilt lazy-diagonalization sketch
   against your own analysis. Its elements: **(i)** the fixed-code stage
   schedule `i = pair(j, r)` — every code recurs at infinitely many stages,
   so the alleged decider's constants (`C_α`, `C₁`, `c₀`) are **fixed**
   along its own subsequence and no padded-index selection occurs (your
   first proposed option); **(ii)** the `f`-adaptive ladder
   `T*_i := (f(ℓ_i + 1) + ℓ_i + 1)²`, `ℓ_{i+1} := 2^{(T*_i)²}`, located by
   **bit-length arithmetic with capped witness runs**, where an unfinished
   capped `f`-witness run itself decides the comparison (`ℓ_{i+1} > n`) —
   your "stop evaluating the next value when the current allowance is
   exhausted"; check the amortized locator ledger and your own oscillating
   interior example against it; **(iii)** the **self-clocked** mid-rung —
   the fixed interpreter core under `D`'s own fused `K·(g n + 1)` countdown
   with `K` independent of the code, cut branches rejecting — so
   `D ∈ NTIME (g+1)` holds by construction, and the chain (3.3) needs only
   that the *relevant* branches finish, which the domination hypothesis's
   `f(n+1)` addend supplies at the fixed assembled constant
   `A* := C_α·(C₁·c₀ + C₁ + 1) + 1`; **(iv)** the top rung at
   `T*_i ≥ C₁·(c₀·f(a) + 1)` eventually (a square against fixed constants
   — the hypothesis's `f n` addend instantiated at the stage bottom `a`,
   exactly your "also require the bound for `f(a)`"), with `BF`'s
   exponential cost beaten by `g n ≥ n = 2^{(T*_i)²}` along the
   subsequence. Verify each inequality chain and flag any remaining
   quantifier slip; the statements themselves are unchanged.
2. For the **minors**: verify the `2 · 27` record count with the scaled
   parser guard (finding 3); the arbitrary-time canonizer route with no
   polynomial claim (finding 4); the **amortized** countdown with the
   `Σ ν₂(j) ≤ t` ledger and the significant-end representation named
   (finding 5); `O_N((k+1)(t+1))` (finding 6); the honest timeout-polarity
   explanation — cut branches reject, no all-branch completion claim, the
   backward direction through the original decider's halting (finding 7);
   "every **positive** `A`" (finding 9). Finding 8 was a **pack erratum**
   (the round-1 pack wrongly asserted `g 0 = 0` impossible under
   `TimeConstructible`): acknowledged here — shipped packs are never
   edited — and the `g + 1`/`hpos` seam stands as the deterministic
   precedent documents.
3. Report anything the repairs broke or newly misstate, same table and
   severity scale. The round-1 notes (the monotone-equivalence
   qualification, the oscillating-bounds strengthening disclosure) are
   retained as declared.

Sources as in round 1 ([AB09] §1.4, §2.1.2 + Exercise 2.6, §3.2 with
Figure 3.1; [Coo72], [BGW70] through [AB09]).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `TuringMachine/NDCodes.lean` (the existence sketch's record count and canonizer route) and `Diagonalization/NTimeHierarchy.lean` (the rebuilt hierarchy sketch, the timeout-polarity and amortized-clock bullets, the universal and normal-form sketch corrections, the showcase wording) |
| Unchanged, re-attached | every declaration of both files (byte-identity checkable in the diff) and the round-1 context set |
| Declared, out of scope | the concurrent §12/P3.2/P4.3 repairs in the same commit range (disjoint files, own rounds); tactic proofs |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **major** — per-code constants vs padded indices: no law preserves cost under padding | Fixed-code scheduling: the stage schedule runs code `α_j` at every stage `i = pair(j, r)`, so the decider's code — and hence `C_α` — is literally the same at infinitely many stages; the domination hypothesis is instantiated once, at the fixed assembled constant. Padding never enters |
| 2 | **major** — the ladder/locator was not computable within the allowance | The explicit recurrence `T*_i := (f(ℓ_i+1) + ℓ_i + 1)²`, `ℓ_{i+1} := 2^{(T*_i)²}` over `f`'s witness, compared against `n` by bit-length arithmetic with **capped runs whose failure itself decides the comparison**; completed stages sum geometrically, the final incomplete evaluation is capped, and `D`'s global `K·(g n + 1)` self-clock makes class membership hold by construction — separating the two obligations your report distinguished (uniform cost of `D`; eventual success for the fixed code) |
| 3 | minor — `2 · 9` records | `2 · 27 = 54` per state, with the parser guard scaled |
| 4 | minor — the polynomial canonizer is not received | The sketch follows the arbitrary-time mirror (`MathlibBridge` supersedes its polynomial variant); no polynomial ND canonizer claimed or needed |
| 5 | minor — per-tick decrement cost is unbounded | "Amortized", with the `Σ_{j≤t} ν₂(j) ≤ t` borrow ledger and the significant-end/zero-test representation named, in both the design bullet and the universal's sketch |
| 6 | minor — `O_N(k·t)` vanishes at `k = 0` | `O_N((k+1)·(t+1))`, with the zero-tape case named |
| 7 | minor — "the timeout polarity never bites" is wrong | The honest explanation: runaway guess branches exist even for total deciders and are cut; cut branches **reject**, which never creates a false positive; accepting witnesses finish within the forward bound; the backward direction truncates at the *original* decider's all-branch budget |
| 8 | minor — the pack's `g 0 = 0` claim | **Pack erratum acknowledged** (`timeConstructible_id` is the counterexample); the `g + 1` and `hpos` seam retained as in the deterministic precedent |
| 9 | minor — "fails for every `A`" | Now "fails for every **positive** `A`", with `A = 0` noted vacuous |
| 10-11 | notes | Retained as declared: the monotone-case equivalence and the genuine nonmonotone strengthening; the square showcase as the chosen alternative, not a rounding of `n^{3/2}` |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p33-r2-sweep.log`, revision recorded
  at start: `9a92fa1a`): both modules, 0 `error:` lines, fresh `.olean`s,
  exactly **7** `declaration uses 'sorry'` warnings (NDCodes 1,
  NTimeHierarchy 6).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`):
  `Diagonalization` 0 FAIL / 0 WARN over 4 files; `TuringMachine` 0 FAIL
  (size WARNs as recorded in the §12 round-2 pack).
* Statement-freeze baseline: commit `9a92fa1a`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p33-r2-findings.md`; the gate closes on zero blockers and
majors.
