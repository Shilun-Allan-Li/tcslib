# External audit pack — Chapter 4, phase P4.3 (`PSPACE`-completeness and the space hierarchy), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P4.3 — `PSPACE`-hardness and -completeness (Definition 4.9), the QBF carrier
and its serialization, `TQBF` and the Stockmeyer-Meyer theorem (Theorem 4.13)
with the packaged adjacency-formula half of Claim 4.4(2), the space-bounded
universal machine (Exercise 4.1), the space hierarchy theorem (Theorem 4.8),
`L ⊊ PSPACE`, `SPACE(n+1) ≠ NP` (Exercise 3.2, normalized), and Zermelo
determinacy (Exercise 4.10). Statement phase per `workflow.md` §2-3; the gate
closes on a round with zero blockers and zero majors.

Audited at commit `200f4693` (branch `complexity/arora-barak-ch3-4`). Under
audit: seven files — `TCSlib/Complexity/Formulas/{QBF,QBFEncoding}.lean`,
`TCSlib/Complexity/ClassPSPACE/{TQBF,Games}.lean` with the phase's new
`ClassPSPACE.lean` facade, `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`,
and the extended `Formulas.lean` facade — **12 sorried statements** (QBF 1,
QBFEncoding 1, TQBF 5, Games 1, Hierarchy 4; the facades carry none) **and
14 definitions** (`Quant`, `QBF`, `truthAux`, `truth`; `quantBit`,
`quantOfBit`, `encode`, `decode`; `PSPACEHard`, `PSPACEComplete`, `TQBF`;
`Game.playOut`, `FirstWins`, `SecondWins`).

**Provenance** (a maintainer execution claim — verify it by
`git diff 572304e5 200f4693` over the seven files): the five Lean modules and
the new `ClassPSPACE` facade are byte-identical to their landing commit
`572304e5`, except (a) `Hierarchy.lean`'s facade-status Design bullet,
refreshed at `3a511a6f` (status prose only — the facade-freeze claim became
false when the P4.1 gate closed), and (b) **a landing erratum repaired at
`1e089e53`**: the `Formulas.lean` facade extension of `572304e5` had appended
its two QBF imports **after** the module docstring — invalid Lean — and the
landing sweep had not included the facade module, so the error went
undetected. It was repaired in place (imports moved into the header block,
`## Contents` rows added for `QBF`/`QBFEncoding`), with a decision-log row
recording the repair and the adopted sweep-hygiene consequence: every gate
sweep lists its touched facades explicitly — this pack's sweep does. And
(c) **a review repair at `0a1982a0`**, caught by this pack's assembly-time
name verification and applied before shipping (the P3.2
review-repairs-before-gate pattern): `QBF.lean`'s
`truth_exPrefix_iff_satisfiable` sketch cited `eval_congr_of_lt_numVars`
under `Std.Sat.CNF`; the chapter-2 lemma lives in the `Complexity`
namespace. Sketch prose only. (The `200f4693` review repairs touch only the
concurrent P4.2 surface — no P4.3 file.)

**Layering caveat, stated plainly**: `TQBF.lean` and `Hierarchy.lean` import
the **phase-P4.2 surface** (`SpaceComplexity/ConfigGraph.lean` — `coreSum`,
`configBound`, the configuration-graph dictionary; attached verbatim as
context), whose own statement gate is running **concurrently**
(`audits/ch4-p42-pack.md`). Audit P4.3's statements against that surface as
given; findings against the P4.2 definitions themselves are welcome and will
be filed to that round, labeled as such — they do not block this gate unless
they falsify a P4.3 statement. Also concurrent: the §12 routine layer
(`audits/routine-infra-pack.md`) — several sketches name §12 catalog/loop
routines as fill engines — and the P4.4 pack (disjoint files). Closed context
this phase sits on: **P4.1** (`audits/ch4-p41-resolutions.md` — the
`SPACE`/`NSPACE` classes, `SpaceConstructible` with the bundled `logSpace`
floor), **P0** (`audits/ch34-p0-resolutions.md` — the received
`TimeHierarchy` surface: the fixed code scheme, the `CodePrefix` discipline,
the `f²` time hierarchy, at commit `f70c57c2`'s reception), and the chapter-2
`Formulas`/`ClassNP` layers (closed campaign).

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **a QBF semantics whose index threading or
free-variable totalization makes `TQBF` a different language than the
book's** (fallback polarity, prefix-versus-`numVars` mismatches), and **a
universal/hierarchy statement whose quantifier order lets the simulated
machine's constant depend on the input** (the `C`-after-`α` order is the
point). Blind restatements for all 14 definitions; true-as-stated arguments
for all 12 sorried statements; at least **5 adversarial instantiations**; no
blanket approvals. Sources: [AB09] §4.2 (Definitions 4.9-4.10, Examples
4.11-4.12 and 4.15, Claim 4.4(2), Theorem 4.13, Exercise 4.10 / §4.2.2),
§4.1.3 (Theorem 4.8, Exercise 4.1), and Exercise 3.2; [SM73] and [SHL65] are
cited through [AB09] — no external text required.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p43-sweep.log`, revision recorded at
  start: `200f4693`): all seven modules — the two facades listed explicitly,
  per the erratum's sweep-hygiene rule — 0 `error:` lines, fresh `.olean`s,
  exactly **12** `declaration uses 'sorry'` warnings (QBF 1, QBFEncoding 1,
  TQBF 5, Games 1, Hierarchy 4; both facades 0).
* Style lint, two logs: `audits/logs/ch4-p43-stylelint.log` — the
  `Formulas` tree 0 FAIL / 0 WARN over 5 files and the `ClassPSPACE` tree
  0 FAIL / 0 WARN over 2 files — and `audits/logs/ch4-p42-p44-stylelint.log`
  (shared with the concurrent P4.2/P4.4 packs) — 0 FAIL / 0 WARN over the
  42 files of the `SpaceComplexity` tree, `Hierarchy.lean` included. The
  per-tree linter does not see facade files, which sit one level up
  (`Formulas.lean`, `ClassPSPACE.lean` — the house convention; the
  `SpaceComplexity.lean` facade is likewise outside its tree's log).
* Statement-freeze baseline: commit `200f4693`.
* Drafting provenance: maintainer-drafted.

## Known deviations and design decisions (declared — verify each, flag others)

1. **CNF matrix as the QBF carrier** (decision CH34-Q5): Definition 4.10
   allows an arbitrary unquantified matrix; the campaign takes the CNF
   restriction *as the carrier* (the chapter-2 `Std.Sat.CNF ℕ`). `TQBF`'s
   hardness pays the Tseitin step inside the reduction; a general-formula
   carrier remains future work.
2. **Prenex by construction**: the prefix is a `List Quant`, and quantifier
   `i` binds variable `i` — the prefix binds an initial segment of `ℕ`.
   Non-prenex formulas are out of scope (the book's polynomial-time prenex
   conversion, p. 83, is not formalized).
3. **Free variables read `false`**: matrix variables at or beyond the prefix
   length evaluate at the all-`false` base assignment — totalization in the
   chapter-2 `codeFallback` spirit. [AB09] considers only closed formulas;
   closed consumers never rely on it.
4. **`decode`'s fallback `⟨[], CNF.fallback⟩` is TRUE** (the empty CNF
   evaluates `true`), so non-well-formed strings lie **in** `TQBF` — the
   same polarity as the chapter-2 `SAT` fallback convention, declared there
   and here.
5. **Claim 4.4(2) existentially packaged** (`exists_adjacency_codec_cnf`),
   with two declared deviations, both argued harmless to Theorem 4.13:
   (i) codec length `O(s + n)` rather than the book's `O(S)` — a one-hot
   input track keeps adjacency *local* (the book's `O(S)` presumes the
   non-local binary head encoding of Claim 4.4(1)); (ii) CNF size bounded
   polynomially rather than linearly in `s + n` — the reduction needs only
   polynomial and emittable. The codec and family have one consumer (the
   hardness fill); D6-style promotion to named definitions is recorded for
   when a second consumer appears (the P4.4 `PATH` encoding is the
   candidate).
6. **Definition 4.9 over `≤ₚ`** (the chapter-2 `PolyTimeReducible`); the
   logspace-reduction variant ([AB09, Exercise 4.9]) is phase P4.4's.
7. **The space-universal machine carries a `+ logSpace n` clock addend**
   versus Exercise 4.1's literal constant-factor bound — the
   configuration-count clock's bits; a declared deviation presuming the
   standing `S(n) > log n` convention (p. 79). The time is existential
   (halting only), with no stated bound.
8. **`space_hierarchy` at constant-factor hypothesis strength**
   (`∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n` — no square, no log: the space
   story's advantage over the received `f²` time hierarchy). Both
   constructibility hypotheses are carried for fidelity to the book; the
   sketch's proof consumes only `g`'s (recorded there, and explicitly seeded
   to this audit — question 7).
9. **`SPACE_linear_ne_NP` at the `n + 1` normalization** per the P0
   positive-bound convention (the literal `SPACE(n)` is the zero-work-tape
   class). The `NP` `≤ₚ`-closure the sketch uses is a named derived
   obligation (from `Complexity.mem_NP_iff_exists_length_le`); neither
   inclusion between the two classes is claimed, matching the book's remark.
10. **Games**: `n` alternating binary moves, a total win predicate, no draws
    (finite games with draws reduce by splitting the draw outcome);
    `determined` states the disjunction only — mutual exclusion is
    deliberately not claimed.

## Specific questions (prioritized)

1. **`truthAux`**: blind-restate the recursion; check the `Function.update`
   accumulation and the index threading (quantifier `i` binding variable
   `i`; the recursion passes `i + 1`); verify that `truth ⟨[], m⟩` reduces
   to evaluation at the all-`false` assignment.
2. **`truth_exPrefix_iff_satisfiable`**: is `m.numVars ≤ n` the right
   hypothesis — what breaks without it? Check both directions'
   update-agreement argument; instantiate at `n = 0` and at a prefix longer
   than the matrix's `numVars`.
3. **`encode`/`decode`**: the pair alignment, `quantOfBit ∘ quantBit = id`,
   and whether `decode_encode` is strong enough for `TQBF`'s consumers — no
   injectivity-of-`encode` claim is stated; is one needed anywhere?
4. **`exists_adjacency_codec_cnf` — THE heavyweight**: blind-restate the
   full quantifier prefix (`C` before `n, s` before the codec and `φ`);
   check the windowed-configuration hypotheses (head positions AND nonblank
   cells within `[-s, s]`, for both `c` and `d`), the placement of
   injectivity inside those hypotheses, the
   eval-on-concatenated-codes-with-`getD`-`false` convention,
   `φ.numVars ≤ 2 ·` the code length, and the `(φ.map List.length).sum` size
   measure. Crucially: the equivalence is
   `φ.eval … = true ↔ M.tm.step c = d` — check the deterministic step
   convention at halted configurations (`step` of a halted configuration;
   does the formula then assert `d = c`, and is that the faithful reading of
   Claim 4.4(2)'s adjacency?).
5. **`TQBF_mem_PSPACE` and `TQBF_PSPACEHard`**: the linear-space evaluator's
   ledger; the `ψᵢ` midpoint recursion with the `∀`-trick, the per-level
   fresh-variable scheme, the size ledger, and the final truth-preservation
   induction (`ψᵢ` true iff reachability within `2^i`) — and is
   `PSPACEHard`-over-`≤ₚ` exactly Theorem 4.13's claim?
6. **`space_universal`**: blind-restate the two-clause statement; the first
   clause's shape (hypothesis "some output computed within space `s`", then
   the universally quantified output — sound for deterministic machines?);
   the `C`-per-`α` quantifier order; the `+ logSpace` addend's necessity and
   harmlessness; adversarial `α` (junk codes — what does the scheme's
   `decode` fallback give?).
7. **`space_hierarchy`**: is `∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n` the
   faithful rendering of the book's `f(n) = o(g(n))` over `ℕ`-valued bounds
   with the `logSpace` floor? The padding/self-application sketch; where
   `f`'s constructibility is (not) used; `LOGSPACE_ssubset_PSPACE`'s
   domination instantiation (`A · logSpace n ≤ n + 1` eventually).
8. **`SPACE_linear_ne_NP`**: the padding argument's statement-level
   soundness — the proof is by contradiction through
   `SPACE(n² + 1) ⊆ SPACE(n + 1)`; check the direction of the padding
   transfer and the hierarchy instantiation. Plus **Games**: `playOut`'s
   parity convention (even plies = player one), the `W`-polarity of
   `SecondWins` (`= false`), and `determined`'s classical content.

Adversarial instantiations to attempt: the empty string and single-bit
strings through `decode` into `TQBF`; a QBF with prefix longer than the
matrix's `numVars`; matrix variables beyond the prefix; `n = 0` games;
`s = 0` in the codec; `f = g` in the hierarchy.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. P4.2-surface findings: same
table, prefixed "[P4.2]", filed to that concurrent round. Findings go
verbatim into `audits/ch4-p43-findings.md`; the gate closes on zero blockers
and majors.
