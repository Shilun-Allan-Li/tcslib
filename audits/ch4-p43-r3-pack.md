# External audit pack — Chapter 4, phase P4.3, round 3 (re-audit of the round-2 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P4.3, round 3. Round 2 (`audits/ch4-p43-r2-findings.md`, attached verbatim,
alongside round 1's `audits/ch4-p43-findings.md`) returned **1 blocker,
0 majors, 4 minors, 3 notes**: the quotient restatement cured round 1's
pigeonhole, but the serialized-size bound `C·(s+n+1)^C` was itself
self-contradictory at `n = s = 0`, where the code width equals the budget
and one literal addressing the second block already serializes to `C + 6`.
This round audits the repairs. The gate closes on zero blockers and zero
majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch4-p43-r3-repairs.diff`): **one statement amended in
place** — `exists_adjacency_codec_cnf`'s three serialized-length bounds move
to base `s + n + 2` (your first proposed fix: independent room at the
smallest instance) and its quotient-separation clause becomes an **iff** —
plus the five wording repairs (live self-adjacency, the honest check-count
enumeration, the padded-language restriction, the `Valid`-copy ledger note,
the W1 discard semantics). Everything else is byte-identical to the round-2
surface; the inventory is unchanged (**12 sorried statements, 15
definitions**).

## Brief for the auditor

You have both prior reports. Your deliverables:

1. **For blocker R2-1**: re-run your Section-3 contradiction against the
   amended bounds. At `n = s = 0` the budget is now `C · 2^C` against code
   width `C`: verify a CNF reading both blocks fits (your own singleton
   example `[[(C, true)]]` serializes to `C + 6 ≤ C·2^C` for `C ≥ 2`), and
   that the full validity/adjacency/acceptance families of your Section-4
   construction route fit the `C·(s+n+2)^C` budgets at **every** `(n, s)`
   — including whether one shared `C` now suffices or the independent
   width/size constants of your alternative fix are still needed. Then
   re-check the hardness route's size ledger downstream of the new base.
2. **For R2-2**: the quotient clause is now
   `code x c = code x d ↔ coreSum c = coreSum d` on same-input windowed
   pairs — the factorization reading, matching the docstring; verify the
   iff is right for the intended construction (the codec writes exactly
   the `(x, coreSum)` data, so equal vertices get equal codes), and note
   the round-2 pack's "equal codes required" phrasing is **now** true of
   the statement — a round-2 pack erratum against the then-current clause,
   acknowledged here.
3. **For R2-3/R2-4/R2-5** and notes **R2-6/R2-7**: verify the five wording
   repairs match your proposed fixes (live vertices "need not" be
   self-adjacent; one-hot exclusions quadratic with guarded head-tuple
   enumeration, `(n+2)·(2s+1)^k` cases; the padded language restricted to
   `∃ x ∈ L`; the per-level `Valid` copies and index shifts counted; W1
   capture as discard-to-finite-summary).
4. Report anything the repairs broke or newly misstate, same table and
   severity scale.

Sources as in rounds 1-2 ([AB09] §4.2, §4.1.3, Exercise 3.2).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `ClassPSPACE/TQBF.lean` (the amended codec statement and its docstrings, the hardness/codec sketch repairs) and `SpaceComplexity/Hierarchy.lean` (the padded-language display, the two W1 wording repairs) |
| Unchanged, re-attached | the other five P4.3 files and every other declaration of the two repaired files (byte-identity checkable in the diff) |
| Declared, out of scope | the same commit range contains the concurrent §12/P3.2/P3.3 repairs (disjoint files, own rounds); tactic proofs; dispositions already accepted in round 2 (majors 2-5 of round 1, resolved at statement-gate level there) |

## Per-finding disposition (verify each)

| # | Round-2 finding | Repair |
|---|---|---|
| R2-1 | **blocker** — `C·(s+n+1)^C` strangles the formulas at `n = s = 0` | All three bounds now `C·(s+n+2)^C` — your first proposed fix. At the smallest instance the budget is `C·2^C`; at large `(s, n)` the base change is absorbed by the exponent. The sketch's size sentence records the room explicitly |
| R2-2 | minor — factorization claimed, only one direction stated | The clause is now an iff on same-input windowed pairs; the round-2 pack's overstatement of the then-current clause acknowledged as a pack erratum (shipped packs are never edited) |
| R2-3 | minor — "live vertices are not self-adjacent" | Both sites now say live vertices **need not** be self-adjacent (your stationary silent live loop) |
| R2-4 | minor — linear check count inferred from the listed tracks | The codec sketch now gives the honest enumeration: quadratic one-hot exclusions, transition checks over the `(n+2)·(2s+1)^k` guarded head-position tuples jointly with the state/scanned-symbol cases, polynomial — not linear — totals |
| R2-5 | minor — the padded-language display omitted `x ∈ L` | Now `L' := {y \| ∃ x ∈ L, y = pairEncode x (replicate \|x\|² true)}` |
| R2-6 | note — count all `Valid` copies and index shifts | The hardness sketch's size sentence counts the per-level copies, the two base guards, and the unary-index shifts |
| R2-7 | note — W1 capture must not buffer | Both Hierarchy sketches specify discard-to-finite-summary, never buffering the emitted word |
| R2-8 | note — attestation posture | Unchanged: this round again attaches the repair diff; build claims remain maintainer attestations |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p43-r3-sweep.log`, revision recorded
  at start: `9a92fa1a`): all seven modules, both facades listed, 0 `error:`
  lines, fresh `.olean`s, exactly **12** `declaration uses 'sorry'`
  warnings (QBF 1, QBFEncoding 1, TQBF 5, Games 1, Hierarchy 4).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`): `Formulas`
  0 FAIL / 0 WARN over 5 files; `ClassPSPACE` 0 FAIL / 0 WARN over 2
  files; `SpaceComplexity` 0 FAIL / 0 WARN over 42 files.
* Statement-freeze baseline: commit `9a92fa1a`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p43-r3-findings.md`; the gate closes on zero blockers and
majors.
