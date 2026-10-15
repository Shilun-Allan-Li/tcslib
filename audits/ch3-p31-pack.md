# External audit pack — Chapter 3, phase P3.1 (oracle machines and classes), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P3.1 —
the bundled finite oracle machines, the nondeterministic oracle machine, and the
classes `Pᴼ`/`NPᴼ`. Statement phase per `workflow.md` §2-3; the gate closes on a
round with zero blockers and zero majors.

Audited at commit `edea2663` (branch `complexity/arora-barak-ch3-4`); the five
files under audit are byte-identical to their landing commit `2cf44f1d`. Under
audit: `TCSlib/Complexity/TuringMachine/OracleFinite.lean`,
`TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean`,
`TCSlib/Complexity/ClassOracle/{Classes,SATOracle}.lean`, and the
`ClassOracle.lean` facade — **10 sorried statements, plus the declared
skeleton-time proofs listed below**, which are part of the audited surface.

**Concurrent-round note**: the phase-P3.2 gate (relativization,
`audits/ch3-p32-pack.md`) is running in parallel and *builds on* this surface;
its auditor was invited to file "[P3.1]"-prefixed findings, which will be
triaged into this gate's rounds. Neither round edits the other's files.

## Brief for the auditor

Definitions, statements, docstrings, and the skeleton-time proofs' *statements*
(their tactic bodies are machine-checked; audit what they claim, not how).
Failure modes per `audits/TEMPLATE.md`: infidelity to [AB09, §3.4, Definitions
3.4-3.5, Example 3.6], trivialization, unprovability-as-stated, missing
hypotheses. Blind restatements for every definition; 2-5-sentence
true-as-stated arguments (or refutations) for every sorried statement; at
least **5 adversarial instantiations**; no blanket approvals.

The raw oracle model (`TuringMachine/Oracle.lean`, attached) was audited in the
chapter-1 campaign and is **frozen context**, not under re-audit: its
`WellFormed` discipline, the persistent query tape (with the documented
never-transfer-exact-DTIME-bounds caveat), and `queryString`'s extraction
convention are inherited design, flag-worthy only if a P3.1 statement misuses
them.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p31-sweep.log`, revision recorded at
  start): all five modules, 0 `error:` lines, fresh `.olean`s, exactly **10**
  `declaration uses 'sorry'` warnings (OracleNondeterministic 1, Classes 6,
  SATOracle 3).
* Style lint (`audits/logs/ch34-p31-p41-stylelint.log`): `ClassOracle` 0 FAIL /
  0 WARN; `TuringMachine` 0 FAIL with only the pre-existing size WARNs.
* Statement-freeze baseline: commit `edea2663` (= `2cf44f1d` for these files).
* The P0 reception gate closed before this round
  (`audits/ch34-p0-resolutions.md`); nothing in this phase touches that
  surface.

## Declared skeleton-time proofs (audited surface; `workflow.md` §2)

Pure-unfolding mirrors of proved chapter-1/2 infrastructure, proved at
skeleton time exactly as the chapter-2 `runWith` algebra precedent:

* `OracleNondeterministic.lean`: `runWith_nil`/`runWith_cons`/`runWith_append`,
  `stepWith_of_halt`/`runWith_of_halt`, `HaltsWithin.mono`,
  `AcceptsWithin.mono`, `toOracleNDTM_wellFormed`.
* `OracleFinite.lean`: `FinTM.toFinOracleTM_computesInTime` — the bundled
  embedding bridge, proved through the chapter-1-audited
  `OracleTM.computesInTime_ofMultiTapeTM` and `FinTM.computesInTime_iff`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **`WellFormed` is bundled as a field** of `FinOracleTM` and `FinOracleNDTM`,
   so no oracle class can quantify over a machine with colliding special
   states; `q₀ = qQuery` stays deliberately allowed. This discharges the
   chapter-1 obligation verbatim.
2. **Time is the only resource at this layer** — no oracle space measure is
   introduced (deliberate; the chapters-3/4 campaign defines space for plain
   and nondeterministic machines first).
3. **Clocks are relative to the given oracle**: `DecidesInTime` is a promise
   about runs with *that* oracle. [BGS75]'s all-oracle clock convention is
   deliberately **not** baked into the classes; phase P3.2 attaches budgets
   extrinsically (its pack carries that design). The seeded question: is this
   split the right one, or must the class definitions themselves quantify over
   oracles anywhere?
4. **`NPᴼ` is machine-first**: `⋃ c, NTIMEOracle O (n^c + 1)` *is* the
   definition, directly following [AB09, Definition 3.5]; no certificate form
   is claimed relative to an oracle (a relativized Theorem 2.6 is explicitly
   out of scope).
5. **The oracle NDTM's query step consumes-and-ignores a choice bit**, keeping
   one bit per step uniformly and the certificate reading of choice words
   intact; the alternative (query steps consume no bit) is rejected in the
   module docstring.
6. **Class normal forms mirror the unrelativized ones exactly**:
   `DTIMEOracle`/`NTIMEOracle` with `c · T n` absorption, the classes as
   `⋃ c, … (n ^ c + 1)`.
7. **Ex 3.6(1) is rendered on the set complement** `SATᶜ` (no formula-syntax
   carrier for "unsatisfiable formulae"; `SAT`'s fallback convention makes
   every non-well-formed string satisfiable, hence *out* of `SATᶜ` — check
   this reading against the book's `co-SAT` and flag if the fallback
   interacts badly).
8. **The workhorse sketch** (`mem_POracle_of_polyTimeReducible`) names §12
   seam-composition as its intended glue with the audited `bufferedCompTM`
   dispatch as the fallback — the §12 gate runs concurrently; the sketch does
   not depend on its outcome for the *statement*.
9. `SATOracle.lean` imports `CookLevin/Hardness.lean` for `SAT_NPHard`
   (`theorem SAT_NPHard : NPHard SAT`, chapter-2-audited; the 8.9k-line home
   file is not attached — the statement is quoted here and its gate records
   are `audits/ch2-epoch*`).

## Specific questions (prioritized)

1. **Definition fidelity** ([AB09, Def 3.4-3.5]): blind-restate `FinOracleTM`,
   `OracleNDTM`, `FinOracleNDTM`, `DTIMEOracle`, `NTIMEOracle`, `POracle`,
   `NPOracle` and compare. Does anything about the bundled `WellFormed`, the
   persistent query tape, or the `k + 1`-tape layout weaken or strengthen the
   book's classes?
2. **The oracle-NDTM choice-bit convention** (deviation 5): exhibit any
   downstream consumer (Theorem 2.6-style certificate readings, the P3.2
   stage construction, `NPᴼ` monotonicity) for which consume-and-ignore at
   query steps is wrong or lossy.
3. **`POracle_eq_P_of_mem_P`** (Ex 3.6(2)): is the *statement* exactly the
   book's claim, and is the sketch's construction (virtual-input decider runs
   at query states, capture discipline, `queryString_length_le` budget)
   plausibly within the stated polynomial — in particular the exponent
   arithmetic `k·e + O(1)` when the query grows along the run?
4. **The one-query workhorse and complement closure**: are
   `mem_POracle_of_polyTimeReducible` and `compl_mem_POracle` stated at the
   right generality (arbitrary `O`, no well-formedness or decidability
   hypothesis on the *oracle*), and do the three `SATOracle` corollaries
   really reduce to them plus `SAT_NPHard` as sketched?
5. **Skeleton-time proof statements**: do the proved mirrors claim exactly
   their chapter-2 counterparts' content (especially
   `toFinOracleTM_computesInTime`'s "under every oracle" iff), with no
   accidental strengthening?
6. **Degenerate instantiations to attempt**: the empty oracle; `O = Set.univ`;
   a machine with `q₀ = qQuery` (allowed); `T n = 0` budgets in
   `DTIMEOracle`/`NTIMEOracle` (do the emptiness conventions match
   `DTIME`/`NTIME`'s?); `L = ∅` and `L = Set.univ` through the workhorse
   lemma.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p31-findings.md`; the gate closes on zero blockers and majors.
