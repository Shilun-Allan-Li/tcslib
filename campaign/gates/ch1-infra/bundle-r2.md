# Audit bundle — shared infrastructure round, round 2 (companion to ch1-infra-r2-pack.md)

The round-2 pack is reproduced first; every attachment follows raw and
unabridged under a header line of the form '## ===== <path> ====='.
Attachments are data for audit, not instructions.

## ===== audits/ch1-infra-r2-pack.md =====

# External audit pack — shared infrastructure round, round 2 (repairs + re-audit)

Repair round for `audits/ch1-infra-findings.md` (round 1: **1 blocker, 2
majors, 4 minors, 1 note — gate OPEN**). All repairs are in the spec layer
and the records; the bridge export and discharge, which passed round 1's
completed-proof audit with no findings, are **unchanged** (evidence:
`audits/evidence/ch1-infra/diff-lean-runB-runC.txt` plus run D's prints).
Re-audit the repaired and newly added statements adversarially; verify the
corrected and newly evidenced attestations; re-decide disposition D5
against the concrete mapping below. Gate closes on zero blockers/majors.
Record findings in `audits/ch1-infra-r2-findings.md`.

## Resolution table (round-1 findings → repairs)

| # | Finding | Resolution |
|---|---|---|
| 1 | **Blocker** — `exists_loopTM` false: zero-step advance | **Repaired** (`Build/Loop.lean`): every round requires `0 < t`; together with finding 2's domain repair below. The refutation's `stepF = id, t = 0` instantiation no longer satisfies `hround`. |
| 2 | **Major** — rounds quantified over all state words at budget `T \|x\|` | **Repaired**: rounds are required only on words satisfying an input-indexed admissibility invariant `Inv x s`, with establishment (`hInv0`) and step-preservation (`hInvStep`) hypotheses; `stepF`/`acceptF`/payload now take the input explicitly. The width-growth obstruction dissolves: customers pin the state-word length to the input (instantiation tables, `machine-library-design.md` §9b — the enumerator and split-search parameterizations the finding requested). |
| 3 | **Major** — D5 unsupported: no dynamic assembly, no result-bearing search | **Repaired**: new contracts P13 `computesFunInTime_pairConcat` (the D-WRAP shape, `pairEncode x u ↦ x ++ u`), P14 `computesFunInTime_pairDup`, and the combinator C1 `computesFunInTime_pairMapSnd` (payload transformed, head retained); new `exists_loopFindTM` (first accepting orbit point's payload, `[]` on exhaustion); P10's narrowing recorded (§9b); P10's sketch rewritten as an explicit `exists_loopFindTM` instance with full instance data. D5 re-issued below as a customer-to-contract mapping. |
| 4 | Minor — countdown exhausts before the first orbit point | **Repaired** (sketch): the initial anchor entry is free; debiting starts with the second entry, so rounds `0, …, R \|x\|` complete and `R = 0` (`Nat.bits 0 = []`) still checks `s0 x`. The auditor-validated amortized-borrow budget argument is now cited in the docstring. |
| 5 | Minor — P5 harvest sketch emits degree `e + 1` | **Repaired** (sketch): harvest with loop parameter `e − 1` for `e > 0`; constant emission chain for `e = 0`; the same indexing convention named in the `polyBits` sketch. |
| 6 | Minor — attestation 4 labeled character counts as bytes | **Erratum acknowledged; corrected attestation supplied.** The round-1 figures (4,022 / 625) were Unicode character counts; the UTF-8 byte counts are 4,085 / 651 — matching the auditor's own recount. `audits/evidence/ch1-infra/byte-attestation.txt` now gives chars, bytes, and SHA-256 per delimited slice, old and new: both slices hash-identical. The round-1 pack is preserved unmodified per precedent. |
| 7 | Minor — "import leaves" literally false | **Erratum acknowledged; claim restated.** Correct claim: *outside the Build subgraph, the only direct importer of any Build module is the `TuringMachine` facade.* Whole-tree unfiltered grep evidence: `audits/evidence/ch1-infra/import-grep.txt` (9 hits: intra-Build imports, the four facade lines, and nothing else). The theorem-dependency evidence (headline prints) is retained as the separate, stronger claim for the named theorems. |
| 8 | Note — historical/customer evidence absent | **Supplied in this bundle**: the `e8dd3e57` git diffs for `Universal.lean` (append-only, zero deletions) and `TMSAT.lean`; the `a418f586` and `d576814c` historical `Loop.lean` texts; the run-A and run-B sweep logs; both kernel-traversal attestation programs (now committed under `audits/programs/`); the full style-lint output; the Chapter-2 sources holding `stripCertificate`/`certificateSplit` (`ClassNP/NP.lean`) and `enumInc`/`enumMachine_contracts` (`ClassNP/EXP.lean`) for the vocabulary-equality check; the batch-C report carrying the D4 promotion request; and `backlog.md` §2's audit-mandated inheritance index for the E3/E4 obligations. The two file-size escalation records are quoted in the attestations below. |
| — | Wrappers module prose said "three contract theorems" | Fixed: four. |

## Corrected and extended maintainer attestations (verify or challenge)

1. **Elaboration.** Run D (`audits/logs/ch1-infra-r2-sweep.log`): full
   fresh-olean 57-module sweep at the repair commit, zero `error:` lines,
   exactly **50** admission warnings — 22 in Build (4 wrapper, 3 loop, 15
   primitive) and 28 elsewhere, i.e. run C's 46 − 18 + 22. Runs A/B/C logs
   attached or committed as before (A: 47; B: 46; C: 46).
2. **Axioms.** `audits/logs/ch1-infra-r2-axioms.log`, produced by the two
   **attached, committed programs** (`audits/programs/ch1-infra-*.lean`):
   exactly **25** `sorryAx` prints — the 22 Build contracts and the three
   TMSAT D-site targets; the five Chapter-1 headlines, both Convention
   lemmas, the export, and the discharged bridge print the standard
   triple; the root-traversal assertions all pass unchanged.
3. **Freeze (historical, now evidenced).** `diff-universal-e8dd3e57.patch`:
   one hunk at end-of-file, **zero deleted lines** — every pre-existing
   `Universal.lean` declaration byte-identical. `diff-tmsat-e8dd3e57.patch`:
   the complete historical record of the relocation + docstring append +
   `sorry` replacement; `byte-attestation.txt` pins both relocated slices
   by SHA-256 (identical) with corrected units.
4. **Scope of this repair round.** `diff-lean-runB-runC.txt` and the run-D
   commit's diff: the only Lean sources changed since run B are the three
   Build modules edited for the repairs (`Loop.lean` in the pack commit;
   `Loop.lean`/`Primitives.lean`/`Wrappers.lean` in the repair commit) —
   the bridge-side sources are untouched since their audited state.
5. **Topology** (restated per finding 7): outside the Build subgraph, the
   only direct importer of any Build module is the facade
   (`import-grep.txt`, unfiltered).
6. **Policy.** `audits/logs/ch1-infra-r2-lint.log` (full output attached):
   0 FAIL; the one WARN is `TMSAT.lean` at 1,206 lines. The two size
   escalations on record: *Universal.lean* — "2831 lines — escalation
   recorded: the brief forbade splitting and ~1100 lines are
   stopped-interpreter administrative copies forced by per-module `match`
   auxiliaries" (ch1 plan, epoch-4A row); *TMSAT.lean* — "justified here
   per policy: exclusive single-file ownership during the fill forces the
   concrete polynomial machine and its run invariants in-file; any
   extraction is a serial maintainer decision at epoch merge" (ch2 plan,
   epoch-2 checkpoint row).

## D5, re-issued: customer-to-contract mapping (approve or challenge)

`m n := C·(n+1)^c` abbreviates the relevant certificate-width polynomial;
"W1/W3" are the capture and timed-branch wrappers; "glue" is the decision
layer over `DecidesInTime` (design §6, fills alongside).

| Customer obligation | Library coverage |
|---|---|
| 2A `enumMachine_contracts` (enumerator) | `exists_loopTM` at the §9b enumerator instantiation (`Inv` = exact width `m \|x\|`; `stepF` = `incFixed` with stall; fuel `2^(m n) − 1`, bits = `replicate (m n) true`); W1 for the captured verifier call inside the body; P5 for the startup width evaluation; the in-place `incFixed` carry as the fuel counter. |
| 2B `choiceVerifier ∈ P` (⊆-direction) | P10/`splitSolve` at `(C, c)` for the unique split; the batch's own proved simulation core as the body (harvest); W1 + W3 guards; P4/P5 for the arithmetic; glue. |
| 2B reverse direction (`NP_subset_iUnion_NTIME`) | **Partially covered by design**: the deterministic phases (assembly, verifier simulation) use the same pieces; the nondeterministic guessing table and branch-correspondence argument are NDTM-side and remain bespoke — the library never claimed the NDTM model. |
| 2C `pairedVerifier ∈ P` | `pairValid` guard (W3) + `pairFst`/`pairSnd` + P4 + P5 + `pairLenCheck` + `pairConcat` + W1 verifier call + glue. |
| 2C `paddedVerifier ∈ P` | P10 (`exists_loopFindTM` instance, payload `pairEncode x v`) + `stripLast` + `pairLenCheck` (the original-bound re-check against the threaded original input) + W1 verifier call + glue. |
| 2D `D-MEM` | Iterated `pairFst`/`pairSnd` for the quadruple parse; `pairMapSnd` with the length counter for the unary-to-binary clock conversion while retaining the request; `pairLenCheck`-style checks; W1 simulator call; W3 guards. |
| 2D `D-WRAP` | `pairValid` guard + **`pairConcat`** + W1 captured verifier + W3 with constant-reject branch for the malformed `[false]`. |
| 2D `D-EMIT` | **`pairDup`** + `pairMapSnd` (payload ↦ the paired unary runs, via P5-unary instances and P2 for the exact-`Q` three-case table) + `pairEncodeFixed α₀` for the outer layer. |
| E3 padding cluster | P3 `prepend` (the padding map itself), P10 family for the padded-split recognition, the loop for scan machines. |
| E4 emitter | `exists_loopTM`/`FindTM` for the stage loops; W1 is the six-stage output-silence contract's engine; P5's exact unary emissions for the length ledger; P2/P3 for fixed emissions. |
| Clearing (ex-P12) | Body-restores-scratch discipline (§3) with the trivial clear sweep as part of the loop fill's toolkit — recorded, not a public contract. |

## What is under audit, round 2

1. **The repaired loop contracts** (`exists_loopTM`, `exists_loopFindTM`):
   attempt refutation again. Known attack surface the maintainer already
   re-checked, for your independent verification: zero-step advances
   (excluded by `0 < t`); seam-to-seam cycles under `stepF x s = s`
   (consistent — the host counts entries and exhausts fuel);
   noncomputable `acceptF` (makes `hround` unsatisfiable, the theorem
   vacuous, not false); trivial `Inv := True` (reinstates the strong
   hypothesis — the theorem remains true, merely hard to instantiate);
   `q₀ = anchor` with nonempty `s0` (makes `hstart` unsatisfiable);
   payload `[]` collisions in the find form (the conclusion's function is
   still well-defined). Also check the budget realizability argument
   again under the input-indexed invariant, and that the two §9b
   instantiation tables genuinely satisfy every hypothesis (in particular
   `hInvStep` under the stall conventions) and produce the customers'
   conclusion shapes.
2. **The three new data-plumbing contracts** (P13, P14, C1): truth and
   realizability at the stated linear / `n + Tg n` budgets, the
   malformed-`[]` clauses under append-only output, and C1's monotonicity
   usage.
3. **The revised sketches** (P5 indexing, P10 instance data, countdown):
   internal consistency with the unchanged statements.
4. **The corrected attestations and new evidence** (byte attestation,
   diffs, grep, programs, lint): verify from the attached artifacts; the
   round-1 "unverified" items should now each be decidable.
5. **D5 as re-issued**: approve, or name a specific customer obligation
   still uncovered.
6. **Vocabulary equality** (round-1 §"pure functions", left uncertified):
   with `ClassNP/NP.lean` and `ClassNP/EXP.lean` now attached, check
   `splitAtLastTrue` against `stripCertificate`, `solveSplit` against
   `certificateSplit`, and `incFixed` against `enumInc` for semantic
   agreement sufficient for the fills' equality lemmas.

Unchanged and **not** re-audited: the bridge export and discharge proofs
(round-1 verdict: no error found), the model files, `loop_run`, and the
15 round-1-passed contracts other than where the findings touched their
sketches. Severity scheme as always; findings to
`audits/ch1-infra-r2-findings.md`; this pack is immutable once sent.

## Verification appendix (runs and manifest)

* Run A — `audits/logs/ch1-build-spec-sweep.log` (attached): 57/57, 0
  errors, 47 admissions, at `a418f586`.
* Run B — `audits/logs/ch1-bridge-export-sweep.log` (attached): 57/57, 0
  errors, 46 admissions, at `e8dd3e57`.
* Run C — `audits/logs/ch1-infra-sweep.log` (committed; round-1 bundle):
  57/57, 0 errors, 46 admissions, at `d576814c`.
* Run D — `audits/logs/ch1-infra-r2-sweep.log` (attached): 57/57, 0
  errors, 50 admissions, at the repair state under audit.
* Axioms — `audits/logs/ch1-infra-r2-axioms.log` (attached), from the two
  committed programs (attached): 25 `sorryAx` prints exactly; traversal
  PASS; exit 0.
* Lint — `audits/logs/ch1-infra-r2-lint.log` (attached): 0 FAIL, 1
  pre-escalated WARN.
* Bundle manifest — **35 attachments** after the pack: the round-1
  findings and round-1 pack (2); the 4 Build modules, the design
  document, the 6 core model/gadget modules, `Encoding.lean`,
  `TMSAT.lean`, `ClassNP/NP.lean`, `ClassNP/EXP.lean`, the facade, the
  order list, the batch-C report, and `backlog.md` (19); the 7 evidence
  files; the 2 attestation programs; the 5 logs — runs A, B, D, the
  round-2 axioms, and the lint output (7 + 2 + 5 = 14).
  Total 2 + 19 + 14 = 35.


## ===== audits/ch1-infra-findings.md =====

**Chapter-1 infrastructure audit — findings**

**Gate: OPEN — 1 blocker, 2 majors, 4 minors.** One additional note records evidence limitations. The bounded-loop existence theorem is false as stated. The concrete universal-machine export and the Chapter-2 bridge derivation pass this source audit, conditional on the previously audited dependencies specified in the pack.

Audited input: `ch1-infra-bundle.md`, SHA-256 `2b73e447a4abec80a27ad8d50ceea169a39ed34121a2d47c8f8a014c65a3975f`. References below use the original repository paths and their file-local line numbers, not bundle line numbers. `Build/…` abbreviates `TCSlib/Complexity/TuringMachine/Build/…`; other bare machine-module filenames have prefix `TCSlib/Complexity/TuringMachine/`, and `TMSAT.lean` has prefix `TCSlib/Complexity/ClassNP/`. The supplied toolchain claim is Lean 4.25.0 / mathlib `029db123ddaa`; no Lean executable, complete dependency tree, historical source snapshots, or attestation-program sources were supplied in this workspace. This is an independent mathematical/source audit and a recount of supplied logs, not a fresh kernel run. The timed-interpreter internals and the unrelated epoch-2 proofs were not re-audited.

1. **[BLOCKER] `exists_loopTM` is false: a rejecting round may take zero steps.**

   **References:** `Build/Loop.lean:148–178`, especially the existential time at lines 157–162 and the advance equation at lines 170–173; `audits/ch1-infra-pack.md:80–92` (attestation 7).

   The no-mid-round-anchor condition does not require a round to occur. At `t = 0` it is vacuous, and an identity advance satisfies the endpoint equation without constraining what the machine actually does from the anchor.

   Here is a refutation using only computable functions and one-state machines. Choose:

   | Parameter | Value |
   |---|---|
   | `body.k`, `F.k` | `0` |
   | `body.State`, `F.State` | `Unit` |
   | `anchor`, both initial states | `()` |
   | Every body transition | Keep the input head stationary; emit `true`; halt. |
   | Every fuel-machine transition | Keep the input head stationary; emit nothing; halt. |
   | `R n`, `T n` | `0`, `1` |
   | `s0 x`, `stepF s` | `x`, `s` |
   | `acceptF s` | `s.getLast?.getD false` |

   All premises hold, step by step:

   - **Fuel:** `Nat.bits (R |x|) = Nat.bits 0 = []`, which `F` computes in one step.
   - **Startup:** choose `t = 0`. With zero work tapes, `stateWord 0 (s0 x)` is the unique empty-domain function. Thus `body.initCfg x = Cfg.ofWords anchor (stateWord 0 (s0 x))`; the earlier-anchor clause is vacuous.
   - **Accepting round:** if `acceptF s = true`, choose `t = 1`. The body halts with `[true]`. No natural number satisfies `0 < t' < 1`.
   - **Rejecting round:** if `acceptF s = false`, choose `t = 0`. Since `stepF s = s`, `runFrom cfg 0 = cfg` is exactly the required advance equation. Again the anchor clause is vacuous.

   The conclusion therefore supplies one `E` and one constant `c` such that, for **every** input `x`,

   \[
   E(x)=[x.\mathrm{getLast?}.\mathrm{getD}(\mathrm{false})]
   \quad\text{within}\quad c(1+1)(0+2)=4c\text{ steps}.
   \]

   This contradicts the machine model. Take the equal-length inputs

   \[
   x=\mathrm{replicate}(4c,\mathrm{false})\mathbin{++}[\mathrm{false}],
   \qquad
   y=\mathrm{replicate}(4c,\mathrm{false})\mathbin{++}[\mathrm{true}].
   \]

   Initially the input head is at position 1. Before transition `j + 1`, with `j < 4c`, its position is at most `j + 1 ≤ 4c`: every transition moves it by at most one. Positions 1 through `4c` contain `false` on both inputs, and position 0 is blank on both. Induction on `j = 0,…,4c` therefore gives identical control states, input-head positions, work tapes, work-head positions, and accumulated outputs in the two runs. The induction step uses identical read tuples and the deterministic transition table; the equal input lengths give identical clamping. Hence their outputs after `4c` steps are equal. The asserted outputs are `[false]` and `[true]`, a contradiction. This also covers `c = 0`.

   **Repair:** require `0 < t` in the round hypothesis. Merely requiring a work tape does not address the logical loophole: with one tape, a startup can copy `x` to the seam in `2|x| + 2` steps, the anchor can always halt with `[true]` in one step, and `stepF = id` still lets every falsely classified state use `t = 0`. The same hypotheses then allow an arbitrary, even undecidable, `acceptF`. The positive-duration repair must accompany the customer-domain repair in finding 2. Re-audit the repaired statement before any fill.

2. **[MAJOR] The round hypothesis quantifies over arbitrarily long state words at the empty-input budget; it cannot express the intended counter/enumerator rounds.**

   **References:** `Build/Loop.lean:41–52,115–119,157–173`; `machine-library-design.md:154–179`; the increment semantics at `Build/Convention.lean:113–120`.

   The premise is `∀ x s, ∃ t ≤ T x.length, …`, with no invariant connecting `s` to `x`, its length, or the bounded orbit. Consequently `x = []` demands the same fixed bound `T 0` for **all** state-word lengths.

   A concrete obstruction already occurs for an all-rejecting round that increments its fixed-width state. Set `acceptF s = false` and `stepF s = (incFixed s).getD []`. For a body with at least one tape, consider

   \[
   s=\mathrm{replicate}(T(0)+1,\mathrm{true})\mathbin{++}[\mathrm{false}].
   \]

   The target word is

   \[
   \mathrm{incFixed}(s)
   =\mathrm{some}\bigl(\mathrm{replicate}(T(0)+1,\mathrm{false})
   \mathbin{++}[\mathrm{true}]\bigr).
   \]

   In particular, tape cell `T 0 + 1` must change from `false` to `true`. Its head starts at zero and cannot reach and write that cell within `T 0` transitions (`Configuration.lean:199–213`). Thus no such body satisfies `hround`, regardless of its finite-control size or scratch-tape count. This obstruction remains after adding positive round duration.

   The intended enumerator instead has a width bounded in terms of the current input; padding search similarly has a bounded candidate domain. Neither fact appears in this premise. Encoding the original input inside `s` does not solve the problem: the universal quantifier also demands the same long encoded word be handled when the physical input is empty.

   **Repair:** restrict `hround` to the states on the specified bounded orbit, or add an input-indexed admissibility invariant with startup and advance-preservation hypotheses. Permit `stepF`/`acceptF` to depend explicitly on the input if needed, or relate an encoded copy to that input in the invariant. Supply actual enumerator and split-search instantiation statements to verify customer coverage.

3. **[MAJOR] D5's no-loss-of-coverage disposition is not supported by the interfaces: dynamic data assembly and result-bearing search are missing.**

   **References:** `machine-library-design.md:51–62,107–125,154–179,252–265`; `Build/Primitives.lean:119–177,224–244`; `Build/Loop.lean:163–178`; `TCSlib/Complexity/ClassNP/TMSAT.lean:919–926,1145–1152,1183–1190`; `audits/ch1-infra-pack.md:104–109`.

   There are two concrete customer mismatches, independent of the false loop theorem:

   - **P6 does not provide the required data-preserving assembly.** `pairEncodeFixed` fixes the entire first component before the machine is chosen. `pairFst` and `pairSnd` return one component and discard the other; they are not threaded transformations retaining both components. The attached D-WRAP obligation explicitly needs `pairEncode x u ↦ x ++ u` with a malformed-input branch. D-MEM needs `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x (w.take n))`, with variable components; D-EMIT explicitly requires retaining `x` while generating the unary components. Neither a pair-to-concatenation contract nor a timed data-retaining assembly combinator is supplied. Sequential composition alone gives `g(f(x))`; it does not supply simultaneous access to two discarded results.
   - **The advertised P10 construction is not an instance of the loop's public result contract.** P10 must output the selected split, or `[]`. The loop accepts only a body that halts with `[true]`, and its public conclusion exposes only `[any …]`, with `[false]` on exhaustion. It exposes neither the successful state/candidate nor its payload. In particular, a body that emits `pairEncode (w.take i) (w.drop i)` as the P10 sketch instructs does not satisfy the loop's accepting endpoint. A Boolean existence answer does not identify the successful candidate. The original P10 catalog also described search for a supplied predicate, whereas the implemented P10 specializes to a fixed length equation; that narrowing is not listed in §9a.

   These observations do **not** refute the standalone `splitSolve` or parser computability statements: bespoke finite machines can implement them at the stated budgets. They refute the claimed coverage by the proposed public interfaces and the claimed direct P10 instantiation. New internal machinery could repair the situation, but it must be specified rather than counted as already covered.

   **Repair:** provide timed pair-to-concatenation and data-retaining mapping/assembly contracts sufficient for the named D-sites; provide a result-bearing bounded search/loop contract, or explicitly budget and specify P10's separate controller. Record the P10 narrowing. Re-issue D5 against concrete customer-to-contract mappings, including the absent E3/E4 obligations. P7's exact polynomial unary outputs and P8's original-input length check do match their stated narrow uses; that does not establish the whole disposition.

4. **[MINOR] The countdown sketch exhausts before checking the promised initial orbit point.**

   **References:** `Build/Loop.lean:107–110,121–146,175–178`.

   The supplied fuel is `R`, the sketch decrements on **each entry** into the anchor, and borrow-overflow rejects. Applied to the initial anchor entry, this permits only `R` body rounds. At `R = 0`, `Nat.bits 0 = []` immediately overflows and rejects, even when `acceptF (s0 x) = true`; the conclusion requires checking that point.

   **Repair:** run the initial round without debiting fuel and debit on subsequent anchor entries, or initialize the countdown to `R + 1`. Handle the initial anchor explicitly even when startup has time zero. This is a defect in the proposed construction, not a separate refutation of the desired `R + 1`-point semantics.

   The proposed asymptotic budget itself is adequate once the semantic defects are fixed. For successful decrements from `R` down to 1, the borrow length at value `m` is one plus the number of trailing binary zeros of `m`. Thus

   \[
   \sum_{m=1}^{R}\text{trailingZeros}(m)
   =\sum_{j\ge1}\left\lfloor\frac{R}{2^j}\right\rfloor
   \le R.
   \]

   Rewinding over the borrow path changes this only by a constant factor; the final underflow scans the counter width once. Moreover, `hF` and `output_length_le` give `|(Nat.bits (R n))| ≤ T n`. Even the simpler per-round bound `O(T n + counter width)` is therefore `O(T n)`. Fuel/startup, `R n + 1` body rounds, and exhaustion fit a constant multiple of `(T n + 1)(R n + 2)`, with no additional multiplicative logarithm. This validates the budget strategy; it is not a completed Lean construction.

5. **[MINOR] P5's harvest sketch emits the wrong polynomial degree.**

   **References:** `Build/Primitives.lean:84–100`; the supplied harvest interface at `TCSlib/Complexity/ClassNP/TMSAT.lean:500–509`.

   The contract requires exactly `C (n + 1)^e` trues, but its sketch prescribes `e + 1` nested loops of side length `n + 1`, each box point emitting `C` trues. That emits `C (n + 1)^(e + 1)`. The attached `poly_unary_computes c C` explicitly computes exponent `c + 1`, confirming the mismatch. For `C = 1`, `e = 0`, and `n = 1`, the contract wants one true and the described construction emits two.

   **Repair:** for `e > 0`, harvest with loop parameter `e - 1`; for `e = 0`, use the fixed constant-output machine. The available time allowance `c (n + 1)^(e + 1)` remains ample. Make the same indexing convention explicit in the binary-clause harvest. This is a repair to the new sketch, not an audit finding against the old generator's proof.

6. **[MINOR] Attestation 4 labels Unicode character counts as byte counts.**

   **References:** `audits/ch1-infra-pack.md:57–68`; `TCSlib/Complexity/ClassNP/TMSAT.lean:604–677,709–719`.

   The supplied UTF-8 text reproduces the advertised numbers as **character** counts:

   | Precisely delimited current-text region | Unicode characters | UTF-8 bytes |
   |---|---:|---:|
   | From `/-- The canonizer's completed serialization` through the blank separator before `/-- A single timed simulator` | 4,022 | 4,085 |
   | From `theorem timed_universal_quantitative` up to, but excluding, `:= by` (including its preceding space) | 625 | 651 |

   The discrepancy comes from multibyte symbols, including `α`, `∀`, `∃`, and `≤`. Excluding the final space gives 624 characters and 650 bytes for the second region; it does not give 625 bytes.

   **Repair:** correct the units and provide comparisons/hashes of actual byte slices at explicitly stated boundaries for both versions. The counting error does not prove that the relocation changed the lemmas, but the stated byte figures are incorrect and cannot certify byte identity. Historical equality remains unverified for the separate reason in finding 8.

7. **[MINOR] Attestation 5's literal import-leaf claim is false; its intended external-boundary claim needs narrower wording.**

   **References:** `audits/ch1-infra-pack.md:69–75`; `Build/Wrappers.lean:6`, `Build/Loop.lean:7`, `Build/Primitives.lean:7`; `TCSlib/Complexity/TuringMachine.lean:15–18`.

   `Convention` is imported by three other Build modules, so it is not an import leaf and the facade is not its only importer. Among the supplied files, the facade is the only importer **outside Build** of the new Build modules. The complete tree is not attached, so an unrestricted whole-tree grep claim cannot be repeated here.

   Import visibility also differs from theorem dependency: a facade can make admitted declarations available without any particular proved theorem depending on them. The supplied headline axiom prints support the latter, narrower claim for the named theorems.

   **Repair:** state the boundary claim as “outside the Build subgraph, the only direct importer is the facade,” and supply the whole-tree grep evidence. Retain the named theorem-dependency checks as the evidence that those proofs do not use the new admissions.

8. **[NOTE] Several requested historical and customer attestations cannot be independently verified from this bundle.**

   **References:** `audits/ch1-infra-pack.md:32–92,96–109,159–163,190–211`; `audits/logs/ch1-infra-axioms.log:13–21`; `machine-library-design.md:107–120`.

   The manifest correctly describes 19 attachments after the pack, but the following evidence is absent: the pre-export `Universal.lean` and `TMSAT.lean`; the original loop statement; run-A and run-B logs; the environment-traversal programs; the style-lint output and escalation records; the private definitions `stripCertificate`, `certificateSplit`, and `enumInc`; the batch-C promotion report; and the E3/E4 customer briefs. The supplied Lean files cover only part of the 57-module tree.

   Therefore this audit cannot certify either freeze claim, public declaration-order preservation, the claim that only `Loop.lean` changed between runs B and C, exact equality to the three absent private functions, or coverage of every E3/E4 obligation. A current source snapshot and clean axiom print cannot establish a historical byte comparison. The root log lists declaration names, not a reproducible traversal algorithm or per-site records; the three TMSAT `sorry` sites can, however, be checked directly in the attached source.

   **Disposition:** these claims remain **unverified**, not disproved merely because their evidence is missing. Supply the historical slices/diffs and the named source/interface evidence in the repair bundle. No repository access or unrelated proof audit was performed to fill these gaps.

**Statement-by-statement verdicts**

“Pass” below means no false statement or unrealizable stated budget was found by this statement-phase audit; it does not claim that a stub has been filled or kernel-checked. Findings 1–3 qualify customer coverage even where the standalone function is realizable.

| # | Contract and file lines | Truth / realizability verdict |
|---|---|---|
| 1 | `capture_run`, `Build/Wrappers.lean:135–144` | Pass. The capture correspondence commutes with every live source step, including a halting emission. |
| 2 | `redirectTM_computes`, `Build/Wrappers.lean:190–194` | Pass. The register updates before the source halt test; the matching branch halts silently within the same bound. |
| 3 | `redirectTM_live`, `Build/Wrappers.lean:206–211` | Pass. A mismatched final register, including no emission, enters the stationary live state. |
| 4 | `computesFunInTime_cond`, `Build/Wrappers.lean:226–233` | Pass. Separate tape banks preserve blank branch tapes; rewinding the input costs a constant multiple of the decider's run, and the selected branch sees the original input length. No monotonicity premise is needed. |
| 5 | `loop_run`, `Build/Loop.lean:83–96` | Pass, including `N = 0`. The first accepting segment or the final exhaustion segment supplies the verdict within `(N + 1) B`. Zero-length advances do not invalidate this finite summation lemma. |
| 6 | `exists_loopTM`, `Build/Loop.lean:148–179` | **False** (finding 1); intended round domains also excluded (finding 2); countdown sketch needs finding 4's correction. |
| 7 | `computesFunInTime_prepend`, `Build/Primitives.lean:66–69` | Pass. Emit the fixed prefix then copy the input; coefficient may depend on the prefix. |
| 8 | `computesFunInTime_lengthBits`, `Build/Primitives.lean:79–82` | Pass. Binary increments with return to the low-order end have linear total carry cost; empty input yields `[]` and still halts. |
| 9 | `computesFunInTime_polyUnary`, `Build/Primitives.lean:96–101` | Pass as a statement, including `C = 0`, `e = 0`, and empty input. The harvest indexing is wrong (finding 5). |
| 10 | `computesFunInTime_polyBits`, `Build/Primitives.lean:113–117` | Pass. Unary generation followed by linear-time length measurement preserves the stated polynomial degree in time. |
| 11 | `computesFunInTime_pairEncodeFixed`, `Build/Primitives.lean:131–134` | Pass for a fixed first component; does not supply dynamic assembly (finding 3). |
| 12 | `computesFunInTime_pairFst`, `Build/Primitives.lean:145–149` | Pass. Buffer decoded prefix until an aligned separator is found. Malformed input yields `[]`; valid empty first components also yield `[]` by design. |
| 13 | `computesFunInTime_pairSnd`, `Build/Primitives.lean:160–164` | Pass. After a valid aligned separator, every suffix is legal and may be emitted. No valid separator gives `[]`. |
| 14 | `computesFunInTime_pairValid`, `Build/Primitives.lean:173–177` | Pass. Aligned `00`/`11` blocks continue, `01` succeeds, and `10` or a missing/incomplete separator fails. Suffix contents are unrestricted. |
| 15 | `computesFunInTime_pairLenCheck`, `Build/Primitives.lean:191–198` | Pass. Measure decoded component lengths and compare with the exact polynomial; `|a| ≤ |input|` controls the stated budget. Malformed input returns `[false]`. |
| 16 | `computesFunInTime_stripLast`, `Build/Primitives.lean:212–222` | Pass. Buffer before deciding whether a last `true` exists. Validity failures and all-false regions produce `[]`; a successful empty witness still produces a nonempty encoded pair. Even linear-time direct scans suffice for the quadratic allowance. |
| 17 | `computesFunInTime_splitSolve`, `Build/Primitives.lean:237–244` | Pass as a standalone machine statement. Search at most `n + 1` candidates, each with `O((n + 1)^(e + 1))` allowance; output has length at most `2n + 2`. The claimed direct loop instantiation is unavailable (finding 3). |
| 18 | `computesFunInTime_incFixed`, `Build/Primitives.lean:258–261` | Pass. Detect overflow before emitting. Empty input overflows; every successful result is nonempty and has the input width, so `[]` is an unambiguous failure result here. A constant number of scans suffices. |

**Convention, wrapper, and primitive checks supporting those verdicts**

`Cfg.ofWords` and its two proved lemmas (`Build/Convention.lean:75–94`) agree with `Cfg.init` (`Configuration.lean:190–191`) and `bufferTape` (`Simulation.lean:465–488`). The input head is 1, each work head is 0, control is live at the anchor, and physical output is empty. For tape position `z`, the content is `w[z]` when `0 ≤ z < |w|`, and blank otherwise. The initial-configuration lemma reduces using `bufferTape [] = blank`; the tape projection is definitionally reflexive. The general constructor does not assert that every tape is scratch; the loop's `stateWord` assignment is what makes all tapes other than tape 0 blank.

For W1 (`Build/Wrappers.lean:86–143`), the agreement hypothesis supplies the same input move and first `k` tape actions. If the source emits `b`, the capture head at `|pre ++ source.output|` writes `b` and moves right once; `bufferTape_append` gives the next stored word. Otherwise both the word and head stay fixed. The host emits nothing. A live successor is mapped by `emb`, and a halted successor maps to `ret` **after that same transition's emission**. Induction consequently proves the stated correspondence through the first halt. The guard allows the halting endpoint and prevents taking an unconstrained transition from `ret` afterwards. An already halted source at `t = 0` is harmless. Neither injectivity of `emb` nor disjointness of `ret` is needed for this conditional theorem: `hagree` already imposes the necessary consistency. Agreement on all read tuples is stronger than reachable-state agreement, but is a valid compositional table condition.

For `loop_run`, take the least accepting index if one exists below `N`; preceding advance equations compose by `runFrom_add`. Its accepting segment uses at most one additional `B`. If no such index exists, compose all `N` advances and the final exhaustion segment. The respective bounds are at most `(N + 1) B`, and `List.range N` tests exactly indices `0,…,N−1`. At `N = 0`, the conclusion is precisely the exhaustion hypothesis with `[false]`.

The pure functions have the following semantics (`Build/Convention.lean:101–120`): `splitAtLastTrue [] = none`, every all-false word gives `none`, and `u ++ [true] ++ replicate r false` returns `some u`. The function defining `solveSplit` is strictly increasing because, for `i < j`,

\[
i+C(i+1)^e\le i+C(j+1)^e<j+C(j+1)^e.
\]

This remains valid for `C = 0` and `e = 0`. The search includes both endpoints. In particular, at `n = 0`, it succeeds with `i = 0` exactly when `C = 0`. `incFixed` preserves width on success, increments the little-endian value by one, and returns `none` on exactly the all-true words, including the empty word. These facts agree with the disciplines described in the pack; equality to the absent private definitions is not certified.

The pairing default `getD []` deliberately identifies parse failure with a valid empty extracted component. It is not a validity certificate; pipelines must use `pairValid` at the appropriate input stage. `stripLast` instead returns a full encoded pair on success, so even an empty witness is distinguishable from its `[]` rejection.

For `polyBits`, write the unary machine's time as `a(n+1)^(e+1)` and the length machine's time as `b(m+1)`. The latter is monotone. The existing composition theorem (`Composition.lean:367–389`, realized multiplier 2) gives

\[
\begin{aligned}
&2\bigl(a(n+1)^{e+1}+b(a(n+1)^{e+1}+1)+1\bigr)\\
&=2\bigl(a(b+1)(n+1)^{e+1}+b+1\bigr)\\
&\le 2(a+1)(b+1)(n+1)^{e+1},
\end{aligned}
\]

since `(n+1)^(e+1) ≥ 1`. Thus the composition overhead does not increase the claimed exponent.

**Completed-proof audit: export and bridge**

The five lemmas at `TCSlib/Complexity/ClassNP/TMSAT.lean:604–676` are mathematically sound on the supplied definitions. Let `L = (c.decode α).serialize.length` and `H = c.canonizerTime α.length`. The canonizer's completed output and `output_length_le` give `L ≤ H`. The serialized header contains the bit word and initial-state index; its table has a nonempty record for each of `numStates + 1` states. Consequently

\[
|(\mathrm{Nat.bits}\,(c.\mathrm{decode}\,\alpha).\mathrm{numStates})|\le L,
\quad (c.\mathrm{decode}\,\alpha).\mathrm{tm}.q_0.\mathrm{val}\le L,
\quad (c.\mathrm{decode}\,\alpha).\mathrm{numStates}+1\le L.
\]

The table proof uses just one of each state's nine nonempty records, which is a valid lower bound. The flattening induction and the two-bit input-move field establish the needed nonemptiness. No unsupported upper bound on the canonizer's running time is assumed.

Expanding `universalBlockBound` (`UniversalBlock.lean:750–751`), the displayed export coefficient is

\[
\begin{aligned}
&3|\alpha|+H+L+2|\mathrm{bits}(\mathrm{numStates})|+2q_0+16
  +3L+5(\mathrm{numStates}+1)+20+14\\
&=3|\alpha|+H+4L+2|\mathrm{bits}(\mathrm{numStates})|+2q_0
  +5(\mathrm{numStates}+1)+50\\
&\le 3|\alpha|+H+(4+2+2+5)L+50\\
&=3|\alpha|+H+13L+50\\
&\le 3|\alpha|+14H+50.
\end{aligned}
\]

Here `numStates` and `q₀` are the decoded machine's state-count parameter and initial-state index. Thus the thirteen bounded terms and all constants are accounted for: `1 + 3 + 2 + 2 + 5 = 13` and `16 + 20 + 14 = 50`.

The new export (`Universal.lean:2861–2899`) chooses `timedUniversalTM c` before `α`, `x`, and `t`. Its displayed coefficient is definitionally `timedStartupBound c α + universalBlockBound c α + 14`: the startup expression at lines 2666–2668 has exactly the same left-associated summands. The type ascription at lines 2882–2890 therefore uses the trusted `timed_computes` result directly, without an arithmetic rewrite or an existential-witness bound.

In the success branch, `computesInTime_iff` supplies the halted state and exact output at the deadline, and `timedAnswer` reduces to `true :: output`. In the timeout branch, a halted state would itself yield a completed output via `computesInTime_iff`; the quantified non-halting hypothesis excludes it, leaving `[false]`. Both clauses, including deadline-inclusive success and the zero-deadline timeout, retain the original theorem's meaning. The public proposition uses only Chapter-1 vocabulary. The explanatory docstring accurately describes this derivation.

The discharge (`TMSAT.lean:709–731`) retains the same single simulator, multiplies the coefficient inequality by the nonnegative natural `(t + 1)^2` using `Nat.mul_le_mul_right`, and applies `ComputesInTime.mono` separately to **both** clauses. It makes no inference about an arbitrary witness of `timed_universal`. No error was found in either completed proof under the pack's explicit dependency boundary.

**Numbered maintainer attestations and requested dispositions**

| Item | Independent disposition |
|---|---|
| Attestation 1 — elaboration | Run C's 57 headers are unique, numbered 1–57, and match the supplied module order exactly. Recount: 0 `error:` occurrences; 46 declaration-level admission warnings, 18 in Build and 28 elsewhere; final `SWEEP_PASS modules=57` at log line 930. Runs A/B, fresh-olean execution, toolchain pin, and historical admission changes are not independently verifiable from the supplied artifacts. |
| Attestation 2 — axioms | Exactly 21 axiom-print lines contain `sorryAx`: 18 Build contracts and the 3 TMSAT targets. The five named Chapter-1 headlines and both new completed theorems print only the standard triple. The source has exactly the three disclosed TMSAT sites: D-MEM at line 964 and D-WRAP/D-EMIT at lines 1152/1190; NP-completeness applies its two parents at line 1204. The displayed root lists match these claims, but the opaque-value traversal implementation and the historical “unchanged” claim cannot be independently checked. The 46 sweep warnings count declarations, not individual `sorry` expressions. |
| Attestation 3 — Universal freeze | **Unverified.** The new theorem is at the end of the namespace and its derivation passes, but no old source or commit diff is attached. This cannot establish zero deletions, one-hunk history, or byte identity of pre-existing declarations. |
| Attestation 4 — TMSAT freeze | **Incorrect byte counts; otherwise unverified historically.** See finding 6. The five current lemmas precede the bridge, and the new docstring retains the escalation paragraph followed by an explicitly historical discharge note. Neither relocation identity nor residual-file identity can be inferred without the baseline. |
| Attestation 5 — topology | **Literal claim false; narrower supplied-file claim supported.** See finding 7. The order has Convention/Wrappers/Loop at positions 9/10/11 after Composition (8), and Primitives at 26 after Encoding (25). |
| Attestation 6 — policy | All 18 current contracts have sketches; two sketches need findings 4/5's corrections, and P10 needs finding 3's interface correction. Current file sizes are 2,901 lines for Universal and 1,206 for TMSAT. Style-lint results, earlier sizes, and escalation records are not supplied. Wrappers' module prose at lines 27–29 also says “three contract theorems,” although it contains four; correct this bookkeeping typo. |
| Attestation 7 — loop repair | Both added hypotheses are present. The fuel-machine premise repairs arbitrary fuel materialization and bounds counter width. The anchor restriction still permits the zero-step refutation, and neither addition supplies the required state-domain invariant. The repaired theorem fails this audit. The original version and unchanged-other-contract claim remain historically unverified. |
| D4 — promotion subsumption | **Accept semantic/time-bound subsumption.** `|w| + n + 1 ≤ (|w| + 1)(n + 1)`, since the difference is `|w| n`. Likewise `2|α| + n + 3 ≤ (2|α| + 3)(n + 1)`, with difference `(2|α| + 2)n`. `pairEncode α x` is exactly prepend by the doubled `α` plus separator. These are weaker uniform linear budgets, not literally the same sharp contract. The absent private source/report prevents a historical harvest comparison. |
| D5 — catalog refinements | **Do not approve.** Findings 2/3 identify explicit customer-interface gaps. P7 covers the displayed exact polynomial emission values, and P8 checks the correct original-input length bound. General assembly, result-bearing search, and the status of clearing support still need explicit customer mappings. Full E3/E4 coverage cannot be certified without those briefs. |

**Notation glossary.** `++` denotes list concatenation; `|w|` is list length; `replicate(r,b)` is the list of `r` copies of bit `b`; `trailingZeros(m)` is the number of low-order zero bits of a positive integer; `O(f)` denotes a constant multiple of the displayed bound, with machine parameters fixed. In the counterexample, `x` and `y` are the two explicitly displayed equal-length inputs and `c` is the claimed loop-machine constant. In the composition calculation, `a` and `b` are the unary-generator and binary-length-machine time coefficients. In the bridge calculation, `L` is the decoded serialization length, `H` is its canonizer time bound, and `numStates`/`q₀` abbreviate the decoded machine's state-count parameter/initial-state index. Other names are those of the audited declarations.


## ===== audits/ch1-infra-pack.md =====

# External audit pack — shared infrastructure round: machine-construction library spec layer + the timed-universal bridge export

Audits the Chapter-1 infrastructure landed 2026-10-03 on
`complexity/arora-barak-ch1`: the **machine-construction library's spec
layer** (`TCSlib/Complexity/TuringMachine/Build/{Convention,Wrappers,Loop,
Primitives}.lean`, design document `machine-library-design.md`, frozen with
user-resolved decisions and spec-phase refinements §9a) and the
**bridge-protocol step-3 maintainer action** — the new public
`Turing.timed_universal_concrete` at the end of `Universal.lean` and the
discharge of the Chapter-2 bridge `Complexity.timed_universal_quantitative`
in `TMSAT.lean`. Three commits: `a418f586` (spec layer), `e8dd3e57` (bridge
export + discharge), and the pack commit (one pre-pack spec repair to the
loop combinator, disclosed as attestation 7). This is **statement-phase
auditing for the library** (the 18 contracts are sorried; their fills come
later and get their own round) and **proof auditing for the export and the
discharge** (both fully proved). Gate closes on zero blockers/majors.
Record findings in `audits/ch1-infra-findings.md`.

**Evidence separation / scope boundary.** `timed_computes` and the entire
timed-interpreter construction below the export were audited at the
Chapter-1 epoch-4 gate (CLOSED, `audits/epoch4-resolutions.md`) and are
**not re-audited here** — this round audits the *derivation* of the export
from them and the public statement's fidelity. Likewise the epoch-2 fill
checkpoints (four partial batches, integrated 2026-10-03) are campaign
material for the later epoch-2 gate, not this round; they appear here only
as the provenance of the bridge coordination (`tmsat_concrete_coefficient`
was delivered proved by batch 2D and is **in scope** — it is now
load-bearing for a proved public theorem).

## Maintainer-side attestations (verify or challenge)

1. **Elaboration.** Three full fresh-olean 57-module sweeps at Lean 4.25.0
   / mathlib `029db123ddaa`, each zero `error:` lines: run A at `a418f586`
   (47 admissions = 29 campaign + 18 new contracts;
   `audits/logs/ch1-build-spec-sweep.log`), run B at `e8dd3e57` (46 — the
   bridge admission retired; `audits/logs/ch1-bridge-export-sweep.log`),
   run C at the pack commit (46; `audits/logs/ch1-infra-sweep.log`, the
   authoritative run for the state under audit).
2. **Axiom attestations** (kernel-level; `audits/logs/ch1-infra-axioms.log`
   at the pack tree, with the per-commit historical logs also committed).
   The Chapter-1 headline regression set — `timed_universal`, `universal`,
   `universal_quadratic`, `exists_effectiveMachineCode`,
   `HALT_not_computable` — prints the standard triple, no `sorryAx`.
   `Turing.timed_universal_concrete` and
   `Complexity.timed_universal_quantitative` print the standard triple.
   Exactly **21** `sorryAx` prints: the 18 Build contracts and the three
   TMSAT targets. A kernel-environment traversal (constants' types and
   values, opaque values included) asserts the exact direct-admission
   roots: `TMSAT_mem_NP` at its `D-MEM` site alone, `TMSAT_NPHard` at its
   `D-WRAP`/`D-EMIT` sites, `TMSAT_NPComplete` at exactly those two
   parents, and the epoch-2 regression roots
   (`NP_subset_EXP`/`HALT_NPHard` → `enumMachine_contracts`) unchanged.
3. **Freeze, `Universal.lean`.** The `e8dd3e57` diff of `Universal.lean`
   is **append-only**: zero deleted lines, one hunk at end-of-file (the
   export theorem and docstring). Every pre-existing declaration is
   byte-identical.
4. **Freeze, `TMSAT.lean`.** Byte-level decomposition of the `e8dd3e57`
   diff: (a) the five private serialization lemmas
   (`tmsat_serialization_length`, `tmsat_flatMap_length`,
   `tmsat_action_nonempty`, `tmsat_serialization_parameters`,
   `tmsat_concrete_coefficient`; 4,022 bytes) relocated **byte-identically**
   above the bridge they feed (they were stated below it — a forward
   reference once the bridge acquired a proof); (b) the bridge's public
   statement byte-identical (625 bytes); (c) the bridge docstring extended
   **append-only** with the discharge note (the escalation paragraph is
   retained as audit history); (d) the `sorry` replaced by the proof;
   (e) the residual file byte-identical. Public declaration order
   unchanged.
5. **Import topology.** The four Build modules are import leaves: the only
   importer anywhere in the tree is the `TuringMachine` facade (grep
   attested), so the 18 sorried contracts cannot reach any audited
   material; the headline prints of attestation 2 confirm this at the
   kernel. Order list at 57 modules: Convention/Wrappers/Loop inserted
   after `Composition`, Primitives after `Encoding` (its threaded
   contracts cite the `pairEncode` grammar).
6. **Policy.** Style lint 0 FAIL throughout; every sorried contract
   carries a construction sketch; the size WARNs (`Universal.lean`
   2831 → 2901 and `TMSAT.lean` 1185 → 1206) sit under their previously
   recorded escalations (ch1 epoch-4A; ch2 epoch-2 checkpoint row).
7. **Pre-pack spec repair, disclosed.** The maintainer's pre-pack
   adversarial pass found the loop combinator `exists_loopTM` as landed in
   `a418f586` defective on two counts and repaired it in the pack commit:
   (i) **anchor-entry discipline** — the intended host detects round
   boundaries as entries into the embedded anchor state, so without a
   no-mid-round-anchor-visit clause in the startup and round contracts the
   fuel accounting miscounts and the computed function changes;
   (ii) **fuel materialization** — the statement quantified over arbitrary
   `R : ℕ → ℕ`, which no finite machine can evaluate; a fuel-machine
   hypothesis (`F` computes `Nat.bits (R |x|)` within `T`) was added. The
   statement under audit is the **repaired** one; the `a418f586` form is
   in history for comparison. The other 17 contracts survived the same
   pass unchanged.

## Maintainer dispositions taken this round (review requested)

* **D4 — 2C's shared-lemma promotion requests subsumed.** The epoch-2
  batch-C report requested public promotion of its `prefixTM_computes` /
  `fixedPair_computes`. Catalog entries P3 (`computesFunInTime_prepend`)
  and P6 (`computesFunInTime_pairEncodeFixed`) state exactly those
  contracts (the latter noting `pairEncode α x` is literally a prepend
  instance at the doubled-word-plus-separator prefix). Requested: confirm
  the subsumption — the batch's proved budgets (`|w| + |x| + 1`;
  `2|α| + |x| + 3`) are instances of the stated `c · (n + 1)` forms.
* **D5 — catalog refinements at spec time** (`machine-library-design.md`
  §9a): P6 realized as fixed-encode + threaded extractors; P7 subsumed by
  P5's unary clause; P8 realized in threaded form; P12 folded into the
  loop fill. None touches the six frozen user decisions. Requested:
  confirm no catalog customer (the five open epoch-2 frontiers, the E3/E4
  briefs' named obligations) loses coverage under these refinements.

## What is under audit, and priorities

**A. The library spec surface** (18 sorried contracts + the proved
`Convention.lean`), against the frozen design document. The question is
never "are the proofs right" (there are none yet) but **"is each statement
true, realizable at its stated budget, and the right contract for its
named customers"** — a false or unrealizable spec here poisons every fill
batch built on it.

1. **The seam** (`Cfg.ofWords`, `initCfg_ofWords`, `ofWords_workTapes` —
   proved): is the seam notion sound and forced (state anchor, input head
   1, `bufferTape` words, origin heads, empty output)? Check the two
   proofs; check `bufferTape`'s semantics against the words-from-origin
   reading.
2. **W1 (`captureAction`/`captureCfg`/`capture_run`)**: adversarially
   re-derive the one-step commutation — the halting-transition emission
   (the four private incarnations' recurring trap), the capture-tape head
   arithmetic against `bufferTape_append`, the input-head and
   work-tape components, the silence clause. Is the liveness guard
   (`∀ t' < t, ¬Halted`) exactly right — too weak (equation false at some
   guarded `t`) or needlessly strong? Does the agreement hypothesis
   (`host.tr` on embedded states equals the transformed table **for all**
   read tuples) over- or under-constrain consumers?
3. **The loop** — the round's priority. (a) `loop_run`: truth as stated
   (output accumulation through empty-output rounds; the `(N + 1) · B`
   budget; the `(List.range N).any` semantics including `N = 0`).
   (b) `exists_loopTM` **after the attestation-7 repair**: are the two
   added hypotheses *sufficient* for realizability — re-derive the
   intended construction (fuel via `F` relocated-and-captured; body
   embedded under W1; decrement on anchor entry with **amortized** binary
   borrow, exhaustion as borrow-overflow) and check the stated budget
   `c · (T + 1) · (R + 2)` survives, in particular that the countdown does
   **not** reintroduce a logarithmic factor and that `R n = 0`
   (`Nat.bits 0 = []`) still checks the single orbit point `s0 x`. (c) Is
   the orbit semantics (`stepF^[i]`, fuel `R + 1` points, exhaustion
   `[false]`) the contract the enumerator continuation
   (`enumMachine_contracts`) and the split search (P10) actually need?
4. **Primitive contracts P3–P11**: for each, attempt refutation — a
   malformed input, an edge width, or a budget the construction sketch
   cannot meet. Specific known-sharp spots: the threaded `[]`-rejection
   outputs under append-only output (buffer-before-emit — the sketches
   now say it; check the *statements* don't secretly require emitting
   before validity is known); `splitAtLastTrue`'s pure semantics versus
   the audited Exercise-2.1 marker discipline; `solveSplit` uniqueness
   claims in the docstrings versus the `find?` definition; `incFixed`
   width zero; `pairFst`/`pairSnd` `getD []` on genuinely ambiguous
   malformed classes; `polyBits` through the composition overhead
   `T₂(T₁ n)`.
5. **Vocabulary duplication check**: the pure functions
   (`splitAtLastTrue`, `solveSplit`, `incFixed`) against their Chapter-2
   private counterparts (`stripCertificate`, `certificateSplit`,
   `enumInc`) — same semantics, so the later fills' equality lemmas are
   provable, with no silent divergence (e.g. the strip's behavior on the
   all-`false` region and on `[]`).

**B. The bridge export and discharge** (fully proved).

6. **The export's statement fidelity**: one simulator before code, input,
   and deadline; both `timed_universal` clauses verbatim; the displayed
   coefficient is **definitionally** `timedStartupBound c α +
   universalBlockBound c α + 14` (the proof's single type ascription turns
   on this — check the `timedStartupBound` definition against the
   displayed expression, term by term, associativity included); no
   Chapter-2 notion; no inference from `timed_universal`'s existential
   witness anywhere.
7. **The discharge**: re-derive `tmsat_concrete_coefficient`'s arithmetic
   from `tmsat_serialization_length`/`tmsat_serialization_parameters` and
   the `universalBlockBound` definition (the `14·canonizerTime + 50`
   absorption — count the thirteen bounded terms and the constants);
   check `Nat.mul_le_mul_right` + `ComputesInTime.mono` transfer **both**
   clauses; confirm the relocation left the five lemmas' statements and
   proofs untouched (attestation 4 claims byte-identity — challenge it).
8. **The export's audit flag hygiene**: the docstring's claims (realized
   witness, no witness-bounding, Chapter-2-free) against the proof text.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch1-infra-findings.md`; this pack is immutable once sent.

## Verification appendix (runs and manifests)

* Run A — `audits/logs/ch1-build-spec-sweep.log`: 57/57 PASS, 0 errors,
  47 admission warnings, at `a418f586`.
* Run B — `audits/logs/ch1-bridge-export-sweep.log`: 57/57 PASS, 0 errors,
  46 admission warnings, at `e8dd3e57`.
* Run C — `audits/logs/ch1-infra-sweep.log`: 57/57 PASS, 0 errors, 46
  admission warnings, at the pack commit (the state under audit; run C's
  tree differs from run B's only in `Build/Loop.lean` per attestation 7).
* Axioms — `audits/logs/ch1-infra-axioms.log` (pack tree): the two
  attestation programs (bridge roots + Build spec prints), 21 `sorryAx`
  prints total, traversal PASS, exit 0. Per-commit historical logs:
  `ch1-build-spec-axioms.log` (at `a418f586`),
  `ch1-bridge-export-axioms.log` (at `e8dd3e57`).
* Bundle manifest: the companion `audits/ch1-infra-bundle.md` attaches,
  raw and unabridged, the 4 Build modules, the design document, the 6 core
  model/gadget modules they are stated over (`Configuration`,
  `Deterministic`, `Finite`, `Simulation`, `Sweep`, `Composition`), the 4
  bridge-side sources (`Encoding`, `UniversalBlock`, `Universal`,
  `TMSAT`), the facade, the 57-module order list, and the run-C sweep and
  pack-tree axiom logs — **19 attachments** (4 + 1 + 6 + 4 + 1 + 1 + 2).
  Earlier-run logs and all governance records are committed in the
  repository at the paths named above.


## ===== TCSlib/Complexity/TuringMachine/Build/Convention.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the calling convention

The vocabulary module of the machine-construction library
(`machine-library-design.md`, design frozen 2026-10-03): the single seam
notion that the library's control combinators speak, plus the pure list/
arithmetic functions that the primitive contracts in
`TCSlib.Complexity.TuringMachine.Build.Primitives` are stated against.

**Status: spec phase.** This module is fully proved (definitions and two
glue lemmas); the sibling `Build` modules state sorried contracts against
it. The whole `Build` surface is new Chapter-1 growth, flagged for the
shared infrastructure audit round (with the `Universal` bridge export).

## The seam notion

The model already gives *whole* machines a clean boundary: read-only input,
blank work tapes, append-only output, start at `Turing.MultiTapeTM.initCfg`.
The library therefore needs a configuration discipline only where a
construction crosses an *internal* seam — the round boundary of the loop
combinator and the entry of a wrapped subroutine. `Turing.Cfg.ofWords` is
that discipline: control at a designated anchor, input head at its initial
position, every work tape holding one word from the origin
(`Turing.FinTM.bufferTape`) with its head at the origin, output empty. A
loop body's contract is "`ofWords` in, `ofWords` out", and — per the frozen
design decision — the body *restores its own scratch to blank* (its scratch
words are `[]` on both sides of the contract) rather than relying on a
generic clearing pass.

## Main definitions

* `Turing.Cfg.ofWords` — the canonical seam configuration: anchor state,
  input head at 1, work tape `i` holding word `w i` from the origin, heads
  at the origin, empty output.
* `Turing.splitAtLastTrue` — strip a marker suffix: the prefix before the
  last `true`, or `none` if the word is all `false` (the audited marker
  discipline of the Chapter-2 Exercise-2.1 construction).
* `Turing.solveSplit` — least solution `i ≤ n` of the padding length
  equation `i + C·(i+1)^e = n`, or `none` (the split-search discipline of
  the padding constructions).
* `Turing.incFixed` — little-endian fixed-width binary increment with
  explicit overflow (`none`), width preserved (the enumerator's counter
  discipline; width zero overflows immediately).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape machine model the
  seams are stated over.)
-/

namespace Turing

variable {k : ℕ} {State : Type*}

/-- The canonical seam configuration of the machine-construction library:
control at the anchor state `q`, input head at its initial position `1`,
work tape `i` holding the word `w i` written from the origin
(`Turing.FinTM.bufferTape`), every work head at the origin, and the output
empty. Loop-round and wrapper-entry contracts are stated as equations
between `runFrom` results and `ofWords` configurations; a body that owns
scratch tapes lists them with word `[]` on both sides of its contract
(body-restores-scratch, the frozen design decision 9.2). -/
def Cfg.ofWords {input : List Bool} (q : State) (w : Fin k → List Bool) :
    Cfg k Bool State input :=
  ⟨some q, 1, fun i => FinTM.bufferTape (w i), fun _ => 0, []⟩

/-- A machine's genuine initial configuration is the seam configuration at
its start state with every tape word empty: `Cfg.init` has blank tapes and
`Turing.FinTM.bufferTape [] = fun _ => none`. This is the lemma that lets a
combinator's startup phase begin from a seam rather than from a bespoke
initialization invariant. -/
lemma initCfg_ofWords (tm : MultiTapeTM k Bool State) (x : List Bool) :
    tm.initCfg x = Cfg.ofWords tm.q₀ (fun _ => []) := by
  simp only [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, FinTM.bufferTape_nil]

/-- The seam words of a configuration are read back literally: at a seam,
work tape `i` holds exactly `w i` on cells `0, …, |w i| − 1` and blanks
elsewhere. Unfolds `Cfg.ofWords` for consumers that reason cell-wise. -/
lemma Cfg.ofWords_workTapes {input : List Bool} (q : State)
    (w : Fin k → List Bool) (i : Fin k) :
    (Cfg.ofWords (input := input) q w).workTapes i = FinTM.bufferTape (w i) :=
  rfl

/-- Strip a marker suffix: the prefix of `v` before its **last** `true`, or
`none` when `v` is all `false`. This is the Chapter-2 Exercise-2.1 marker
discipline (split at the last `true`; an all-`false` certificate region is
a rejection), stated once as a pure function so that machine contracts and
the chapter-side semantic lemmas name the same operation. -/
def splitAtLastTrue (v : List Bool) : Option (List Bool) :=
  match v.reverse.dropWhile (fun b => !b) with
  | true :: rest => some rest.reverse
  | _ => none

/-- Least index `i ≤ n` solving the padding length equation
`i + C·(i+1)^e = n`, or `none` when no solution exists. Strict monotonicity
of `i ↦ i + C·(i+1)^e` makes the solution unique; the machine contract
`Turing.FinTM.computesFunInTime_splitSolve` performs this bounded search. -/
def solveSplit (C e n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + C * (i + 1) ^ e == n

/-- Little-endian fixed-width binary increment with explicit overflow:
`incFixed w` is the successor word of the same length, or `none` when `w`
is all `true` (overflow) — in particular width zero overflows immediately,
matching the enumerator's audited counter discipline. -/
def incFixed : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (true :: rest)
  | true :: rest => (incFixed rest).map (false :: ·)

end Turing


## ===== TCSlib/Complexity/TuringMachine/Build/Wrappers.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: wrappers

The output-isolation layer of the machine-construction library
(`machine-library-design.md` §5, W1–W3): the capture/silence discipline
written once, consolidating its four private incarnations
(`universalCaptureTM` in the universal-machine development, the Chapter-2
enumerator's `enumCaptureTM`, the HALT batch's `acceptTM`, and the private
engine inside `TCSlib.Complexity.TuringMachine.Composition.exists_cond`).
The obligation list is the one the phase-1 and phase-4 audits tabulated:
every source emission is captured, **including an emission on the halting
transition**; the wrapper's physical output stays untouched; the completed
source configuration is preserved at the return.

**Status: spec phase.** The two action/configuration transformers and the
derived machine are real definitions; the four contract theorems are
sorried, to be filled from the existing private proofs (harvest) in the
library fill batches. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

## Design

* **W1 (capture)** is *host-parametric*: rather than a closed wrapper
  machine, `Turing.captureAction` transforms one source action into a host
  action (source tapes untouched, emission appended to the last tape,
  silence, halt redirected to a designated return state), and
  `Turing.capture_run` says that **any** host machine agreeing with the
  transformed table on an embedded copy of the source states simulates the
  source in lockstep with its output captured on the last tape. Consumers
  (the loop fill, HALT-style control modifications, the Chapter-2
  continuations) embed the source into *their* controller state type and
  inherit the whole induction. The capture tape holds the full output
  word (tape-capture core, frozen design decision 9.3); reading one bit
  off it is the register corollary, derived at fill time.
* **W2 (halt-redirect)** is the `acceptTM` pattern as a closed
  transformation `Turing.FinTM.redirectTM`: simulate a machine silently
  while remembering the last emitted bit, halt exactly when the source
  halts with the designated bit, and otherwise enter a one-state
  stationary live loop.
* **W3 (timed branch)** is the quantitative form of
  `Turing.FinTM.exists_comp_partial`'s sibling
  `Turing.FinTM.exists_cond`: deciding which branch runs costs the
  decider's budget, and the branch runs on the *same* physical input, so
  no monotonicity hypothesis is needed.

## Main declarations

* `Turing.captureAction`, `Turing.captureCfg` — the W1 transformers.
* `Turing.capture_run` — the W1 lockstep/capture/silence contract (sorried).
* `Turing.FinTM.redirectTM` — the W2 transformation.
* `Turing.FinTM.redirectTM_computes`, `Turing.FinTM.redirectTM_live` — the
  W2 contract pair (sorried).
* `Turing.FinTM.computesFunInTime_cond` — the W3 timed branch (sorried).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the capture discipline is the
  output-isolation folklore every simulation argument of §1.4–§1.7 uses.)
-/

namespace Turing

variable {k : ℕ} {S H : Type*}

/-- W1 action transformer. Transform one source action into a host action
over one extra tape: the source's input move and work-tape actions are kept
on the first `k` tapes; the source's emission, **if any**, is written on
the last tape with a right move (so the capture tape accumulates the output
word from the origin); the host emits nothing; a live source successor is
embedded via `emb`, and a halting source action transfers control to the
designated return state `ret` — on the very transition that may carry the
final emission, which is therefore captured like any other. -/
def captureAction (emb : S → H) (ret : H) (a : Action k Bool S) :
    Action (k + 1) Bool H where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩
    else
      match a.output with
      | some b => (some (some b), SignType.pos)
      | none => (none, SignType.zero)
  output := none
  state := some ((a.state.map emb).getD ret)

/-- W1 configuration correspondence. A source configuration `c`, viewed
inside a host with one extra tape: source state embedded (a halted source
sits at the return state `ret`), same input head, source work tapes on the
first `k` tapes, and the capture tape holding `pre ++ c.output` — the
emissions captured so far after a pre-existing prefix — with its head one
past that word. The host's own physical output is the untouched `out₀`. -/
def captureCfg {input : List Bool} (emb : S → H) (ret : H)
    (pre out₀ : List Bool) (c : Cfg k Bool S input) :
    Cfg (k + 1) Bool H input where
  state := some ((c.state.map emb).getD ret)
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then c.workTapes ⟨i, h⟩
    else FinTM.bufferTape (pre ++ c.output)
  workTapePos := fun i =>
    if h : (i : ℕ) < k then c.workTapePos ⟨i, h⟩
    else ((pre ++ c.output).length : ℤ)
  output := out₀

/-- **W1, the capture contract** (spec, fill pending — harvested from the
four private incarnations). If a host machine's transition table agrees, on
an embedded copy of the source's states, with the capture-transformed
source table, then the host run from a capture configuration *is* the
capture image of the source run, for as long as the source has not halted
before the time in question. Taking `t` to be the source's halting time
instantiates the return clause: the host sits at `ret` with the completed
source configuration preserved, the full source output (halting emission
included) on the capture tape, and the host output still `out₀`; taking
`t` below it gives live lockstep.

**Proof sketch.** Induction on `t`. One host step from a live capture image
applies the transformed action: the first `k` tapes and the input head
update exactly as the source's (`Turing.Action.apply` componentwise); the
capture tape appends the emitted bit, which is
`Turing.FinTM.bufferTape_append` at head `|pre ++ c.output|`; silence keeps
the host output at `out₀`; and the successor state is the embedded source
successor, or `ret` on the halting transition. -/
theorem capture_run {input : List Bool} (tm : MultiTapeTM k Bool S)
    (host : MultiTapeTM (k + 1) Bool H) (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S input) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    host.runFrom (captureCfg emb ret pre out₀ c₀) t =
      captureCfg emb ret pre out₀ (tm.runFrom c₀ t) := by
  sorry

end Turing

namespace Turing.FinTM

/-- W2 transformation: the `acceptTM` control-modification pattern. Simulate
`M` with its output suppressed while a finite register remembers the **last**
emitted bit (`none` before any emission) — updated *before* the halt test, so
a bit emitted on the halting transition counts. When the source halts, halt
if the remembered bit is `haltOn`; otherwise enter the one-state stationary
live loop. Tape count unchanged. -/
def redirectTM (M : FinTM Bool) (haltOn : Bool) : FinTM Bool where
  k := M.k
  State := (M.State × Option Bool) ⊕ Unit
  tm :=
    { q₀ := Sum.inl (M.tm.q₀, none)
      tr := fun q inp work =>
        match q with
        | Sum.inl (s, r) =>
          let a := M.tm.tr s inp work
          let r' := match a.output with
            | some b => some b
            | none => r
          { inputTape := a.inputTape
            workTapes := a.workTapes
            output := none
            state := match a.state with
              | some s' => some (Sum.inl (s', r'))
              | none => if r' = some haltOn then none else some (Sum.inr ()) }
        | Sum.inr () =>
          { inputTape := SignType.zero
            workTapes := fun _ => (none, SignType.zero)
            output := none
            state := some (Sum.inr ()) } }

/-- **W2, the halting clause** (spec, fill pending — harvested from the
HALT batch's `acceptTM_halts_iff`). If `M` completes output `w` on `x`
within `t` steps and the last bit of `w` is the designated bit, the
redirected machine halts on `x` within the same budget with **empty**
output (everything was suppressed).

**Proof sketch.** Lockstep correspondence between `M`'s run and the
redirected run, carrying "register = last emitted bit so far"; at `M`'s
halting transition the register equals `w`'s last bit, so the redirect
halts there. -/
theorem redirectTM_computes {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? = some haltOn) :
    (redirectTM M haltOn).ComputesInTime x [] t := by
  sorry

/-- **W2, the live clause** (spec, fill pending). If `M` completes output
`w` on `x` and `w`'s last bit is *not* the designated bit (in particular if
`w = []`), the redirected machine never halts on `x`: at the source's
halting transition it enters the stationary live loop, which is fixed under
every further step.

**Proof sketch.** Lockstep with the register invariant (register = last
emission so far) up to the source's halting transition; there the register
differs from the designated bit, so control enters the stationary live
state, which every further step fixes (two-line induction). -/
theorem redirectTM_live {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? ≠ some haltOn) :
    ∀ u : ℕ, ¬((redirectTM M haltOn).tm.runFrom
      ((redirectTM M haltOn).tm.initCfg x) u).Halted := by
  sorry

/-- **W3, the timed branch** (spec, fill pending): the quantitative form of
`Turing.FinTM.exists_cond`. If a decider machine computes the test bit
within `T₀` and each branch computes its function within `T₁`, `T₂`, the
conditional function is computable within a constant multiple of
`T₀ + max T₁ T₂ + 1`. No monotonicity hypothesis: the selected branch runs
on the *same* physical input.

**Proof sketch.** Run the decider through the W1 capture discipline (its
verdict on the capture tape, physical output silent), rewind per the
`Turing.FinTM.rewind_from_any` scan, then dispatch on the captured bit into
the two-machine branch union (`Turing.FinTM.branchTM`), which runs the
selected branch from its genuine initial configuration on the shared input.
Constant overhead per phase is absorbed into `c`. -/
theorem computesFunInTime_cond {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  sorry

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Loop.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L; loop redesign §9b): a bounded loop
with tape-resident round state, specified at three granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template. (Round-1 audit:
  Pass.)
* `Turing.FinTM.exists_loopTM` is the **decision combinator**: from a fuel
  machine and a body machine whose startup and rounds are
  `Turing.Cfg.ofWords` seam contracts, one finite machine iterates the
  body under a fuel bound and answers the Boolean "some orbit point
  accepts".
* `Turing.FinTM.exists_loopFindTM` is the **result-bearing variant**: the
  accepting round delivers a payload, and the machine outputs the first
  accepting orbit point's payload (`[]` on exhaustion) — the form the
  split search (catalog P10) and the reduction emitters instantiate.

**Status: spec phase, round-2 repair.** The round-1 audit
(`audits/ch1-infra-findings.md`) refuted the previous combinator: finding
1 (blocker) exhibited a zero-step "advance" (`stepF = id`, `t = 0`) that
made the hypotheses vacuously satisfiable and the conclusion contradict
the input-head information bound; finding 2 (major) showed the round
hypothesis quantified over *all* state words at the budget `T |x|`, which
no body can satisfy for width-growing rounds and which excludes the
intended customers. This revision repairs both:

* every round takes **positive time** (`0 < t`), and
* rounds are required only on **admissible** state words, via an
  input-indexed invariant `Inv x s` that the startup word satisfies
  (`hInv0`) and the advance step preserves (`hInvStep`); customers choose
  `Inv` to pin the state-word width to the input (instantiation tables in
  `machine-library-design.md` §9b).

`stepF`, `acceptF`, and the payload take the input as an explicit first
argument (finding 2's repair guidance): the enumerator's acceptance runs
the verifier on `x ++ s`.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2). A round either **accepts** — halts with its declared
output, nothing emitted earlier — or **advances** to the seam carrying the
stepped state word, in positive time, and in both cases without re-entering
the anchor state strictly between the seam and that endpoint (the host
detects round boundaries as entries into the embedded anchor; the clause is
load-bearing, round-1 attestation 7 and finding 1).

**Countdown discipline** (corrected per round-1 finding 4): the counter is
loaded from the fuel machine's output `Nat.bits (R |x|)`; the **initial
anchor entry is free**, and debiting starts with the second entry, so the
rounds completed before borrow-overflow are exactly `0, …, R |x|` — at
`R |x| = 0` (`Nat.bits 0 = []`) the single orbit point `s0 x` is still
checked before the empty counter overflows. Decrement cost is amortized
(the borrow lengths over a full countdown telescope to `O(R)`, and the
counter width is at most `T |x|` by `Turing.MultiTapeTM.output_length_le`
on the fuel machine), which is what keeps the stated budget at
`(T + 1) · (R + 2)` with no logarithmic factor — the round-1 audit
validated this budget strategy (finding 4, second half).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template;
round-1 audit verdict: Pass, including `N = 0`).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  sorry

end Turing

namespace Turing.FinTM

/-- **The decision loop combinator** (spec, fill pending; repaired per
round-1 findings 1, 2, and 4 — see the module docstring). Hypotheses:

* `hF`: the fuel machine writes `Nat.bits (R |x|)` within `T |x|`.
* `hInv0`, `hInvStep`: the admissibility invariant holds at the initial
  state word and is preserved by the step, so every orbit point the
  conclusion mentions is admissible.
* `hstart`: the body reaches the initial seam within `T |x|` without
  visiting the anchor state earlier.
* `hround`: on every **admissible** state word, the body takes **positive**
  time `t ≤ T |x|`, does not re-enter the anchor strictly before `t`, and
  either halts with the verdict `[true]` (acceptance) or sits at the seam
  carrying the stepped word (advance).

Conclusion: one finite machine answers, within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`, whether some orbit point
`(stepF x)^[i] (s0 x)` with `i ≤ R |x|` is accepted.

**Proof sketch.** The combinator machine runs the fuel machine
relocated-and-captured to lay `Nat.bits (R |x|)` on a counter tape,
rewinds, and embeds the body via the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). The initial anchor
entry is free; each subsequent entry debits the binary counter in place —
amortized borrow, exhaustion exactly at borrow-overflow, so rounds
`0, …, R |x|` run before the exhaustion rejection `[false]`. Acceptance
surfaces as the captured halt and emits `[true]`. `Turing.loop_run` sums
the seam family; the invariant hypotheses confine every round to
admissible words, and positive round duration makes each anchor entry a
genuine round boundary. Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

/-- **The result-bearing loop combinator** (spec, fill pending; added per
round-1 finding 3 — the decision form exposes only a Boolean, which cannot
express the split search's or the reduction emitters' outputs). Identical
skeleton to `exists_loopTM`, except the accepting round halts with the
declared payload `out x s`, and the machine outputs the **first** accepting
orbit point's payload — `[]` on fuel exhaustion, the library's threaded
rejection value. `List.range.find?` returns the least accepting index, which
is exactly the round at which the iterated body first halts.

**Proof sketch.** As `exists_loopTM`, with one change at the surface: on
the captured halt the host replays the entire capture tape (the payload)
as its output instead of the fixed verdict — the W1 core captures the
full output word precisely so that this variant costs nothing extra. A
payload may be `[]`; the conclusion's function is well-defined regardless,
and consumers that need to distinguish success from exhaustion use
nonempty payloads (the split search's `pairEncode` outputs are always
nonempty). -/
theorem exists_loopFindTM (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => [])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Build/Primitives.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the primitive catalog

The instruction set of the machine-construction library
(`machine-library-design.md` §4, P1–P12): the timed string functions every
Chapter-2 fill batch privately rebuilt, stated once as machine contracts.
`Turing.FinTM.computesFunInTime_id` and
`Turing.FinTM.computesFunInTime_const` (in
`TCSlib.Complexity.TuringMachine.Composition`) are catalog entries P1–P2
and already proved; this module states the rest.

**Status: spec phase.** Every theorem below is sorried; roughly half are
harvests — their fills adapt already-proved private constructions from the
Chapter-2 epoch-2 batches (named per entry) — and the rest are new small
machines. Following the house idiom of
`TCSlib.Complexity.TuringMachine.Composition`, the contracts are
existentially packaged; each fill implements a named private machine with
its run invariants and closes the existential. Multi-argument interfaces
go through `Turing.pairEncode`, whose self-delimiting grammar lets a
pipeline stage **thread the original input through its output** — the
`pairLenCheck` and `stripLast` contracts below are deliberately stated in
that threaded form, which is exactly how the Chapter-2 verifier
constructions consume them. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

**Catalog refinements at spec time** (recorded against the frozen design
§4): P6 is realized as the fixed-first-component encoder plus the threaded
extractors/validity test; P7 (replicate) is subsumed by the unary clause of
P5, whose instances are what the emission customers actually consume; P8
is realized in threaded form (`pairLenCheck`); P12 (`clearTM`) has no
standalone string-function contract — clearing is intra-machine and lives
in the loop fill's toolkit. **Round-2 additions** (per round-1 finding 3:
the extractors discard the other component by design, and sequential
composition alone never yields simultaneous access to two results): P13
`pairConcat` (the D-WRAP shape), P14 `pairDup` (the entry stage of
data-retaining pipelines), and the threaded-map combinator `pairMapSnd`;
P10's narrowing is recorded, and result-bearing search is now
`Turing.FinTM.exists_loopFindTM` (`machine-library-design.md` §9b).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
  folklore tape subroutines of the textbook's simulation arguments.)
-/

namespace Turing.FinTM

/-- **P3, prepend a fixed word** (spec, fill pending — harvest: the HALT
batch's `prefixTM`/`prefixTM_computes`, whose promotion the batch formally
requested). Emitting the fixed word `w` and then copying the input is
computable in linear time; the constant may depend on `w`, which is fixed
before the machine.

**Construction sketch.** The fixed emission chain of
`Turing.FinTM.computesFunInTime_const` for `w`, then the one-state copy
scan of `Turing.FinTM.computesFunInTime_id`; the harvest source proves the
exact budget `|w| + |x| + 1`. -/
theorem computesFunInTime_prepend (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) fun n => c * (n + 1) := by
  sorry

/-- **P4, input length in binary** (spec, fill pending — new; the unary
scan is a one-state sweep and the binary counter discipline is the
`Turing.incFixed` carry loop). The little-endian binary representation
`Nat.bits` of the input length is computable in linear time.

**Construction sketch.** One left-to-right input scan driving an in-place
binary counter on a work tape (the `Turing.incFixed` carry discipline, cost
amortized constant per input cell), then emit the counter word. -/
theorem computesFunInTime_lengthBits :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length) fun n => c * (n + 1) := by
  sorry

/-- **P5, polynomial evaluation, unary clause** (spec, fill pending —
harvest: the TMSAT batch's `polyUnaryTM`/`poly_unary_computes`, proved with
budget `(C + 5(e+1) + 4)·(n+1)^(e+1)`). The exact unary value of
`C·(n+1)^e` at the input length is computable within a constant multiple of
`(n+1)^(e+1)`. Its instances are also the exact-emission primitive the
reduction constructions consume (catalog entry P7, subsumed here).

**Construction sketch** (indexing corrected per round-1 finding 5: the
harvest source's `poly_unary_computes` with loop parameter `c` emits
exponent `c + 1`, so this contract harvests with parameter `e - 1`): for
`e > 0`, `e` nested unary loop tapes of side length `n + 1`, installed by
one input scan, the innermost loop emitting `C` trues per box point —
exactly `C·(n+1)^e` in total; for `e = 0` the output is the constant
`List.replicate C true`, a fixed emission chain. A recursive invariant
restores completed inner heads, with loop depth `r` costing at most
`(C + 1 + 5r)·(n+1)^r`. -/
theorem computesFunInTime_polyUnary (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        fun n => c * (n + 1) ^ (e + 1) := by
  sorry

/-- **P5, polynomial evaluation, binary clause** (spec, fill pending —
harvest: the TMSAT batch's composition of the unary generator with the
binary length counter). The little-endian binary representation of
`C·(n+1)^e` at the input length is computable within a constant multiple
of `(n+1)^(e+1)`.

**Construction sketch.** The unary generator above composed with the
binary length counter of `computesFunInTime_lengthBits` through the public
buffered composition (`Turing.FinTM.computesFunInTime_comp`) — the harvest
source's exact route, under the same `e - 1` harvest-indexing convention
as the unary clause (round-1 finding 5). -/
theorem computesFunInTime_polyBits (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        fun n => c * (n + 1) ^ (e + 1) := by
  sorry

/-- **P6, pairing with a fixed first component** (spec, fill pending —
harvest: the HALT batch's `fixedPair_computes`, proved with the exact
budget `2|α| + |x| + 3`; its promotion was formally requested). For a
fixed word `α`, the self-delimiting pairing `pairEncode α x` is computable
in linear time. This is the threading stage: downstream threaded contracts
receive `pairEncode a b` and act on `b` while carrying `a`.

**Construction sketch.** `pairEncode α x` is literally
`(α doubled) ++ [false, true] ++ x`, so this is the prepend primitive at
that fixed word; it is kept as its own contract because consumers cite the
pairing grammar, and the harvest source proves the exact budget
`2|α| + |x| + 3`. -/
theorem computesFunInTime_pairEncodeFixed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x) fun n => c * (n + 1) := by
  sorry

/-- **P6, first-component extraction** (spec, fill pending — new; the
aligned two-bit scan of the `Turing.pairDecode` grammar as a machine). On
a well-formed pair the doubled prefix is undoubled and emitted; on a
malformed input the output is `[]`.

**Construction sketch.** Output is append-only, so the scan must not emit
before the parse succeeds: undouble aligned `00`/`11` blocks onto a work
tape until the aligned `01` separator, then replay the buffer to the
output; any misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairFst :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        fun n => c * (n + 1) := by
  sorry

/-- **P6, second-component extraction** (spec, fill pending — new; the
same aligned scan, emitting the suffix after the separator instead). On a
malformed input the output is `[]`. Iterating this extractor is how the
nested-quadruple parsers of the TMSAT constructions decompose.

**Construction sketch.** Scan aligned blocks without emitting until the
separator is found (validity of the prefix must be known before any suffix
bit may be emitted), then copy the suffix verbatim; a misaligned block
halts silently. -/
theorem computesFunInTime_pairSnd :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        fun n => c * (n + 1) := by
  sorry

/-- **P6, grammar validity** (spec, fill pending — new). The single-bit
test for membership in the `Turing.pairDecode` grammar, the guard stage
every parser pipeline rejects malformed inputs with.

**Construction sketch.** One aligned two-bit scan in finite control; emit
the single verdict bit at the separator or at the first misaligned block.
No buffering is needed — only one bit is ever emitted, at the end. -/
theorem computesFunInTime_pairValid :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        fun n => c * (n + 1) := by
  sorry

/-- **P13, pair to concatenation** (spec, fill pending; round-2 addition
per round-1 finding 3 — the D-WRAP obligation's exact shape). On
`pairEncode x u`, emit `x ++ u`; malformed inputs yield `[]`, the threaded
rejection the downstream guard reads (the reduction wrapper's own
`[false]` rejection is assembled at the decider stage).

**Construction sketch.** Undouble the aligned prefix onto a work tape —
nothing emitted while validity is unknown; at the aligned separator,
replay the buffered first component and then copy the suffix verbatim; a
misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairConcat :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        fun n => c * (n + 1) := by
  sorry

/-- **P14, duplication into a pair** (spec, fill pending; round-2 addition
per round-1 finding 3 — the entry stage of data-retaining pipelines:
the reduction emitter retains `x` while its duplicate feeds the generated
components). Emit `pairEncode x x`.

**Construction sketch.** Two input passes: emit each read bit doubled,
then the separator, then copy the input verbatim. No buffering is needed
— the pairing prefix is valid bit by bit, and every input is legal. -/
theorem computesFunInTime_pairDup :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x) fun n => c * (n + 1) := by
  sorry

/-- **C1, the threaded map combinator** (spec, fill pending; round-2
addition per round-1 finding 3 — the data-retaining assembly the
extractors deliberately do not provide: sequential composition yields
`g (f z)` only, never simultaneous access to a retained component). Given
a machine for `g`, transform a pair's payload while carrying its head
component unchanged; malformed inputs yield `[]`. Monotonicity of `Tg`
converts the payload-length bound `|b| ≤ |z|` into a time bound, exactly
as in `Turing.FinTM.computesFunInTime_comp`.

**Construction sketch.** Parse `pairEncode a b` onto two work tapes,
silent until the separator validates; run the `g`-machine on `b`
relocated-and-captured (the W1 discipline — its output lands on the
capture tape, with length bounded by its running time via
`Turing.MultiTapeTM.output_length_le`); then emit the re-encoded pair:
doubled `a`, separator, captured `g b`. -/
theorem computesFunInTime_pairMapSnd {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        fun n => c * (n + 1 + Tg n) := by
  sorry

/-- **P8, threaded length-bound check** (spec, fill pending — new; the
original-bound re-check discipline of the Exercise-2.1 reverse verifier,
in threaded form). On `pairEncode a b`, decide `|b| ≤ C·(|a|+1)^e` — the
original input `a` travels with the payload precisely so that this bound
is checked against *it*, the audited rule being that merely fitting inside
the enlarged region does not authorize a witness. Malformed inputs answer
`false`.

**Construction sketch.** Parse the two components onto work tapes (the
extractor scans above); lay down `C·(|a|+1)^e` in unary by the
polynomial-evaluation loop; compare against `|b|` by a parallel countdown;
emit the single verdict bit. -/
theorem computesFunInTime_pairLenCheck (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        fun n => c * (n + 1) ^ (e + 1) := by
  sorry

/-- **P9, marker strip** (spec, fill pending — harvest: the semantic layer
is the Exercise-2.1 batch's proved `stripCertificate` family; the machine
is new). On `pairEncode a v`, strip `v` at its **last** `true`
(`Turing.splitAtLastTrue`) and re-emit the threaded pair with the stripped
witness; an all-`false` region or a malformed input yields `[]` (the
rejection the downstream guard reads).

**Construction sketch.** Parse `a` and `v` onto work tapes; locate the
last `true` of `v` by one reverse sweep; then — and only then — emit the
re-encoded pair (doubled `a`, separator, the prefix of `v` before that
marker). All-`false` regions and parse failures halt with nothing
emitted. -/
theorem computesFunInTime_stripLast :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  sorry

/-- **P10, padding split search** (spec, fill pending — new; the bounded
search both padding constructions perform, realizable as a
`Turing.FinTM.exists_loopTM` instance over the polynomial-evaluation
primitive). Search for the unique `i ≤ |w|` with `i + C·(i+1)^e = |w|`
(`Turing.solveSplit`); on success emit the threaded split
`pairEncode (w.take i) (w.drop i)`, and on failure `[]` — rejection when
no length-equation solution exists is the audited obligation.

**Construction sketch** (round 2: an `exists_loopFindTM` instance — the
decision loop exposes only a Boolean and cannot carry the payload,
round-1 finding 3; the narrowing from the catalog's supplied-predicate
search to this fixed length-equation search is recorded in
`machine-library-design.md` §9b). Instance data: round state
`s = List.replicate i true`, the candidate in unary;
`Inv w s := s.length ≤ w.length + 1`;
`stepF w s := if s.length ≤ w.length then s ++ [true] else s` (stall past
the end keeps the invariant step-closed); `acceptF w s` holds iff
`s.length + C·(s.length + 1)^e = w.length`, evaluated by the polynomial
loop and a countdown compare;
`out w s := pairEncode (w.take s.length) (w.drop s.length)` — always
nonempty, so success is distinguishable from the `[]` exhaustion; fuel
`R n := n`, so the orbit is exactly the candidates `0, …, n` and
`List.range.find?` returns the least solution, which strict monotonicity
of `i ↦ i + C·(i+1)^e` makes unique — `Turing.solveSplit`'s own
semantics. -/
theorem computesFunInTime_splitSolve (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  sorry

/-- **P11, fixed-width increment** (spec, fill pending — harvest: the
enumerator batch's `enumCarryTM`/`enumCarry_correct`, proved with cost at
most twice the width plus two). The little-endian fixed-width successor
(`Turing.incFixed`), with `[]` on overflow, is computable in linear time.
The in-place form of the same carry loop is the loop combinator's fuel
counter.

**Construction sketch.** Two passes: the first scan detects overflow (all
trues) — nothing may be emitted while that is unknown; on a live word the
second pass emits falses over the carry prefix, a true at the first false,
and the remainder verbatim. The harvest source's in-place variant costs at
most twice the width plus two. -/
theorem computesFunInTime_incFixed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1) := by
  sorry

end Turing.FinTM


## ===== machine-library-design.md =====

# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `audits/ch1-infra-findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.


## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing


## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header.
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AB09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing


## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing


## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state.
* **Optional-write normalization** (`Turing.Action.apply_workTapes`): the raw
  action-application identity for work tapes, promoted at the epoch-2/epoch-3
  boundary.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing

/-- **Optional-write normalization** (promoted from the epoch-2 fill per the
epoch-2 audit, promotion recommendation 1): applying an action rewrites each
work tape at its head with the proposed write, defaulting to the existing read
when the action declines to write. An explicit `some none` write remains an
erase, while an outer `none` writes back the scanned symbol unchanged. Holds
for every alphabet, state type, action, configuration, and tape index — no
finiteness, liveness, or computation hypothesis. -/
lemma Action.apply_workTapes {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

end Turing

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape (w : List Bool) (z : ℤ) : Option Bool :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil : bufferTape [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat (w : List Bool) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left (w : List Bool) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Appending one emitted bit changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append (w : List Bool) (b : Bool) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    cases m <;>
      simp [virtualMove, virtualNextTag, Cfg.inputSymbol, he, VirtualTag,
        moveInputPos, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs : c.inputSymbol = none := by simp [Cfg.inputSymbol, he]
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [hs']
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [bufferedFirstCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [bufferedFirstCfg, Action.apply, ho]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · simp [bufferedFirstCfg, Action.apply]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [bufferedSecondCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [bufferedSecondCfg, Action.apply, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ b' hb' p tapes heads
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    simp only [MultiTapeTM.step, bufferedFirstCfg, hs, bufferedCompTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply, sub_eq_add_neg]
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Choose the first halting time, which is at most `t₁`.
First-phase lockstep reaches its completed configuration, and determinism
identifies the output with `y`. The exact rewind lemma supplies `|y| + 2` more
steps, retaining the first block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hh : ∃ t, (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none :=
    ⟨t₁, ((computesInTime_iff M₁ x y t₁).mp h₁).1⟩
  let t := Nat.find hh
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ t₁ := Nat.find_min' hh ((computesInTime_iff M₁ x y t₁).mp h₁).1
  have hc : M₁.ComputesInTime x c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = y := hc.output_unique h₁
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t (fun s hs => Nat.find_min hh hs)]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Sweep.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sweep gadgets

The generic zipper/transduction layer for sweep-based tape simulations,
promoted out of the one-work-tape construction at the epoch-2/epoch-3
boundary per the epoch-2 audit's promotion recommendations 2-4 (statements
preserved verbatim; only the `private` modifiers were removed). The
controller-specific representations of that construction (its cell type,
alphabet, and finite control) deliberately stay private in
`TCSlib.Complexity.TuringMachine.Robustness.SingleTape`.

## Contents

* **Tape zippers** (`Turing.FinTM.sweepTape`, `sweepCfg`, `sweepRevCfg`, with
  their read/write/turn identities and the beyond-the-zone variants): a finite
  window of a work tape as two stacks around a frontier, scanned in either
  direction, with arbitrary inactive native input and output.
* **Finite transductions** (`Turing.FinTM.sweepFold`, `sweep_run`,
  `sweep_run_reverse`, `sweepFold_append`, `sweep_generate`): a local
  transition-table hypothesis realizes a complete sweep at exact cost, in
  either direction, returning the full resulting configuration.
* **Indexed transducers** (`Turing.FinTM.indexedVisit`, `indexedFold`, and the
  forward/reverse complete-block specializations): a table-valued control that
  changes only the entry named by each cell. The `Nodup` hypothesis of
  `indexedFold` is load-bearing (epoch-2 audit, recommendation 4): two visits
  to the same index could change the control twice.
* **Source bounds** (`Turing.FinTM.source_bounds`): on an initialized run,
  every work head lies in `[-t, t]` at time `t` and every cell outside that
  interval is blank. Initialized runs only — not asserted for arbitrary
  starting configurations (epoch-2 audit, recommendation 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, Claim 1.6 — the simulation these
  gadgets were built for; the module itself is internal infrastructure.)
-/

namespace Turing.FinTM

/-- A finite tape zipper; the left list is stored nearest-cell first. -/
def sweepTape {A : Type} (z : ℤ) (l r : List (Option A))
    (p : ℤ) : Option A :=
  if p < z then (l[(z - 1 - p).toNat]?).join else (r[(p - z).toNat]?).join

/-- Read the current cell of a zipper. -/
lemma sweepTape_read {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r z = r.head?.join := by
  simp only [sweepTape, lt_self_iff_false, ↓reduceIte, sub_self, Int.toNat_zero]
  cases r <;> rfl

/-- A write followed by a right move transfers one cell to the left stack.
**Proof sketch.** At the written coordinate both sides read the new symbol.
Strictly to its left or right, the old and new list indices differ by one,
exactly compensating for the cons or tail operation. -/
lemma sweepTape_right {A : Type} (z : ℤ) (l r : List (Option A))
    (a b : Option A) :
    Function.update (sweepTape z l (a :: r)) z b =
      sweepTape (z + 1) (b :: l) r := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · have h' : p < z + 1 := by omega
      have he : (z + 1 - 1 - p).toNat = (z - 1 - p).toNat + 1 := by omega
      simp only [sweepTape, if_pos h, if_pos h', he, List.getElem?_cons_succ]
    · have h' : ¬p < z + 1 := by omega
      have he : (p - z).toNat = (p - (z + 1)).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, if_neg h', he, List.getElem?_cons_succ]

/-- A configuration at a sweep frontier, with arbitrary native input and output. -/
def sweepCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x := ⟨q, p, fun _ => sweepTape z l r, fun _ => z, out⟩

/-- A sweep's local write, with the native input and output left stationary. -/
def sweepAct {A S : Type} (q : S) (a : Option A) (d : SignType) :
    Action 1 A S := ⟨0, fun _ => (some a, d), none, some q⟩

/-- The one-cell tape identity lifts to configurations. -/
lemma sweepCfg_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l (a :: r) out) =
      sweepCfg (some q') p (z + 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    exact sweepTape_right z l r a b
  · funext i
    rfl
  · exact List.append_nil _

/-- A finite-state left-to-right transduction, recording both its final state
and its rewritten word. -/
def sweepFold {R C : Type} (visit : R → C → R × C) (s : R) :
    List C → R × List C
  | [] => (s, [])
  | a :: as =>
    let v := visit s a
    let rest := sweepFold visit v.1 as
    (rest.1, v.2 :: rest.2)

/-- A local transition rule realizes a complete finite forward sweep.
**Proof sketch.** Induct on the unprocessed word. One machine step writes the
transduced first cell and moves it to the reversed left stack; the induction
hypothesis processes the tail. Input position and output are preserved at every
step, and the number of transitions is exactly the word length. -/
lemma sweep_run {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .pos)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepCfg (some (state (sweepFold visit s as).1)) p (z + as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read z l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr]
    rw [sweepCfg_right, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- The same zipper viewed while scanning toward decreasing coordinates. -/
def sweepRevCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x :=
  ⟨q, p, fun _ w => sweepTape (-z) l r (-w), fun _ => z, out⟩

/-- Reflection converts the forward zipper identity into a left-moving step. -/
lemma sweepRevCfg_left {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l (a :: r) out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i w
    have h := congrFun (sweepTape_right (-z) l r a b) (-w)
    have he : -(z - 1) = -z + 1 := by omega
    change Function.update (fun w => sweepTape (-z) l (a :: r) (-w)) z b w =
      sweepTape (-(z - 1)) (b :: l) r (-w)
    simpa only [Function.update_apply, neg_inj, he] using h
  · funext i
    rfl
  · exact List.append_nil _

/-- The finite transduction lemma for the return sweep, with the exact cost. -/
lemma sweep_run_reverse {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .neg)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepRevCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepRevCfg (some (state (sweepFold visit s as).1)) p (z - as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, sub_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepRevCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read (-z) l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr, sweepRevCfg_left, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Turning round exchanges the two finite stacks. -/
lemma sweepTape_turn {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r = fun w => sweepTape (-(z - 1)) r l (-w) := by
  funext w
  by_cases h : w < z
  · have h' : ¬ -w < -(z - 1) := by omega
    have he : -w - -(z - 1) = z - 1 - w := by omega
    simp only [sweepTape, if_pos h, if_neg h', he]
  · have h' : -w < -(z - 1) := by omega
    have he : -(z - 1) - 1 - -w = w - z := by omega
    simp only [sweepTape, if_neg h, if_pos h', he]

/-- Concatenating two scans threads the finite control between them. -/
lemma sweepFold_append {R C : Type} (visit : R → C → R × C)
    (s : R) (as bs : List C) :
    sweepFold visit s (as ++ bs) =
      let first := sweepFold visit s as
      let second := sweepFold visit first.1 bs
      (second.1, first.2 ++ second.2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, sweepFold, ih]

/-- A transducer whose state is a table, changing only the entry named by a cell. -/
def indexedVisit {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (s : I → V) (a : I × C) :
    (I → V) × (I × C) :=
  let v := visit a.1 (s a.1) a.2
  (Function.update s a.1 v.1, (a.1, v.2))

/-- On a block with distinct tape indices, each local rule sees the original
table entry. This is the block invariant for both sweeps.
**Proof sketch.** Induct on the index list. The first update does not affect
any remaining index because the list has no duplicates. For the final table,
split an arbitrary queried index into the first index, a tail member, or neither. -/
lemma indexedFold {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (cell : I → C) (is : List I) (hi : is.Nodup)
    (s : I → V) :
    sweepFold (indexedVisit visit) s (is.map (fun i => (i, cell i))) =
      (fun i => if i ∈ is then (visit i (s i) (cell i)).1 else s i,
        is.map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  induction is generalizing s with
  | nil => simp [sweepFold]
  | cons i is ih =>
    obtain ⟨hin, ht⟩ := List.nodup_cons.mp hi
    simp only [List.map_cons, sweepFold, indexedVisit]
    rw [ih ht]
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j
        simp [hin]
      · simp only [Function.update_of_ne hj, List.mem_cons]
        by_cases hm : j ∈ is <;> simp [hj, hm]
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hin hj
      simp only [Function.update_of_ne hji]

/-- Each simulated tape contributes exactly one cell to an interleaved block. -/
lemma indexedFold_block {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s ((List.finRange k).map (fun i => (i, cell i))) =
      (fun i => (visit i (s i) (cell i)).1,
        (List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  simpa only [List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k) (List.nodup_finRange k) s


/-- The return sweep's block rule is valid in reverse tape-index order too. -/
lemma indexedFold_block_reverse {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s (((List.finRange k).map (fun i => (i, cell i))).reverse) =
      (fun i => (visit i (s i) (cell i)).1,
        ((List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))).reverse) := by
  rw [← List.map_reverse, ← List.map_reverse]
  simpa only [List.mem_reverse, List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k).reverse
      (by simpa using List.nodup_finRange k) s


/-- One blank cell can be made explicit at the end of the zipper. -/
lemma sweepTape_nil {A : Type} (z : ℤ) (l : List (Option A)) :
    sweepTape z l [] = sweepTape z l [none] := by
  funext p
  unfold sweepTape
  split
  · rfl
  · cases (p - z).toNat <;> rfl

/-- The forward write identity also applies beyond the stored zone. -/
lemma sweepCfg_right_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepCfg_right q q' p z l r out a b
  | nil =>
    have hc : sweepCfg q p z l ([] : List (Option A)) out =
        sweepCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i
      exact sweepTape_nil z l
    rw [hc]
    exact sweepCfg_right q q' p z l [] out none b

/-- The backward write identity also applies beyond the stored zone. -/
lemma sweepRevCfg_left_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepRevCfg_left q q' p z l r out a b
  | nil =>
    have hc : sweepRevCfg q p z l ([] : List (Option A)) out =
        sweepRevCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i w
      exact congrFun (sweepTape_nil (-z) l) (-w)
    rw [hc]
    exact sweepRevCfg_left q q' p z l [] out none b

/-- A fixed finite sequence of writes, in either direction, takes its exact
length. The hypothesis is the local controller rule, and has no global-run premise. -/
lemma sweep_generate {A S : Type} {x : List A}
    (tm : MultiTapeTM 1 A S) (w : List A)
    (cfg : Fin (w.length + 1) → ℤ → List (Option A) → List (Option A) → Cfg 1 A S x)
    (d : ℤ)
    (hstep : ∀ (i : ℕ) (hi : i < w.length) z l r,
      tm.step (cfg ⟨i, by omega⟩ z l r) =
        cfg ⟨i + 1, by omega⟩ (z + d) (some w[i] :: l) r.tail)
    (z : ℤ) (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    tm.runFrom (cfg 0 z l r) n =
      cfg ⟨n, by omega⟩ (z + d * n) ((w.take n).map some |>.reverse |>.append l)
        (r.drop n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep n (by omega)]
    have hz : z + d * n + d = z + d * (n + 1 : ℕ) := by push_cast; ring
    rw [hz, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, ← List.drop_one, List.drop_drop]
    rfl


/-- Source heads and nonblank cells stay within the elapsed-time interval.
**Proof sketch.** Heads start at zero and move by at most one per step.
A write can only change the cell under an old head, so it cannot create a
nonblank cell outside the larger interval at the next time. -/
lemma source_bounds {Γ : Type} (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ t) ∧
    (∀ i z, z < -(t : ℤ) ∨ (t : ℤ) < z →
      (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none) := by
  induction t with
  | zero => simp [MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    constructor
    · intro i
      have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
      rw [abs_le] at hp
      have := ih.1 i
      push_cast
      omega
    · intro i z hz
      have hz' : z < -(t : ℤ) ∨ (t : ℤ) < z := by omega
      have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by
        have := ih.1 i
        omega
      unfold MultiTapeTM.step
      cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => exact ih.2 i z hz'
      | some q =>
        dsimp only [Action.apply]
        cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
          (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
        · exact ih.2 i z hz'
        · dsimp only
          rw [Function.update_of_ne hne]
          exact ih.2 i z hz'

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: every bound
*adapted from the source* carries an existential constant (purely internal results,
such as the oracle lockstep lemmas, are legitimately exact but never cross a
convention), and every result is self-contained in-model. A formal bridge (a
read-write-output machine variant plus a simulation theorem) will be added if and only
if a downstream result needs it. What this file *does* provide is the buffer-and-flush
technique — an emission can be deferred to a work tape and flushed at the end — which
is what delayed or revisable output looks like *within this model*; whether the
append-only convention matches [AB09]'s read-write one remains formally unestablished,
per the waiver.

The generic simulation gadgets this file's machines are assembled from — emission
chains, control actions, disjoint tape-block embeddings with their lockstep run
lemmas, the input-head rewind, and the two-machine branch union — live in
`TCSlib.Complexity.TuringMachine.Simulation` (split out at the epoch-1/epoch-2
boundary, per the epoch-1 audit findings 5 and 11 and the policy file-size
standard); this file keeps only its concrete machines and their theorems.

## Main results

* Time-bounded combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
* **Partial (guarded) combinators** — the phase-4 API mandated by the phase-3 audit
  (round 2, finding 10 and Argument F: the total-function composition cannot take
  the partially computing universal evaluator as a component):
  `Turing.FinTM.exists_comp_partial` composes two arbitrary machines at the level of
  their halting relations, with the intermediate output buffered on a work tape;
  `Turing.FinTM.exists_cond` branches between two machines on a decided predicate.
  Both are stated untimed; time-bounded refinements are deliberately deferred until
  a result needs them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).state = some () ∧
    (((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (t + 1) =
        (idTM.tm.tr () (some (x[t]'(by omega)))
          ((idTM.tm.runFrom (idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (idTM.tm.runFrom (idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The identity function is computable in linear time: the copy machine halts within
`n + 1` steps having emitted its input verbatim (invariant `idTM_run`, then one
halting step on the boundary blank). -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  refine ⟨idTM, 1, fun x => ?_⟩
  obtain ⟨hstate, hpos, hout⟩ := idTM_run x x.length (le_refl _)
  have h0 : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hsym : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg h0, dif_pos (by omega)]
  have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (x.length + 1) =
      (idTM.tm.tr () none
        ((idTM.tm.runFrom (idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
        (idTM.tm.runFrom (idTM.tm.initCfg x) x.length) := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hstate]
    dsimp only
    rw [hsym]
  have hbase : idTM.ComputesInTime x x (x.length + 1) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout]
      simp
  exact hbase.mono (le_of_eq (one_mul _).symm)

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  refine ⟨constTM w, w.length + 1, fun x => ?_⟩
  obtain ⟨hs, ho⟩ := emit_halts (constTM w).tm w id (fun _ _ _ => rfl)
    ((constTM w).tm.initCfg x) rfl
  have hbase : (constTM w).ComputesInTime x w (w.length + 1) := by
    exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
  exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))

/-- The hardcoded comparator, followed by the chosen fixed-word emission chain. -/
private def ifEqTM (w₀ u v : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w₀.length + 1) ⊕ (Fin (u.length + 1) ⊕ Fin (v.length + 1))
  tm :=
    { q₀ := .inl 0
      tr := fun q inp _ => match q with
        | .inl i =>
          if h : i.val < w₀.length then
            if inp = some w₀[i.val] then
              controlAction .pos (some (.inl ⟨i.val + 1, by omega⟩))
            else controlAction 0 (some (.inr (.inr 0)))
          else if inp = none then controlAction 0 (some (.inr (.inl 0)))
            else controlAction 0 (some (.inr (.inr 0)))
        | .inr (.inl i) => emitAction u (fun j => .inr (.inl j)) i
        | .inr (.inr i) => emitAction v (fun j => .inr (.inr j)) i }

/-- Once the comparator has chosen its output chain, that chain emits the selected
word and halts, independently of the input-head position. -/
private lemma ifEq_finish (w₀ u v x : List Bool) (b : Bool)
    (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x)
    (hs : cfg.state = some (.inr (cond b (.inl 0) (.inr 0)))) (ho : cfg.output = []) :
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).state = none ∧
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).output = cond b u v := by
  cases b
  · simpa only [Bool.cond_false, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm v (fun j => .inr (.inr j))
        (fun _ _ _ => rfl) cfg hs
  · simpa only [Bool.cond_true, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm u (fun j => .inr (.inl j))
        (fun _ _ _ => rfl) cfg hs

/-- Comparison invariant: the first `i` symbols match, and the head is at `i + 1`.

**Proof sketch.** Induct on the number of remaining comparison symbols. A matching
symbol advances the invariant. A mismatch selects the second emission chain. With
no symbols remaining, the boundary blank selects the first chain and an extra
symbol selects the second. The emission-chain lemma supplies the remaining time. -/
private lemma ifEq_run (w₀ u v x : List Bool) : ∀ (r i : ℕ) (hlen : w₀.length = i + r), i ≤ x.length → x.take i = w₀.take i →
    ∀ (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x),
      cfg.state = some (.inl ⟨i, by omega⟩) → cfg.inputPos.val = i + 1 → cfg.output = [] →
      ∃ t, t ≤ r + max u.length v.length + 2 ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).state = none ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).output = if x = w₀ then u else v := by
  intro r
  induction r with
  | zero =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : ¬i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases he : x = w₀
    · subst x
      have hb : w₀[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inl 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inl 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v w₀ true _ hs' ho'
      refine ⟨u.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_true, if_pos rfl] using hf
    · have hx : i < x.length := by
        by_contra hh
        have hxt : x.take i = x := List.take_of_length_le (by omega)
        have hwt : w₀.take i = w₀ := List.take_of_length_le (by omega)
        exact he (by rw [← hxt, ← hwt]; exact hprefix)
      have hb : x[i]? = some x[i] := List.getElem?_eq_getElem hx
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, Option.some_ne_none, ite_false]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf
  | succ r ih =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases hm : x[i]? = some w₀[i]
    · obtain ⟨hx, hbit⟩ := List.getElem?_eq_some_iff.mp hm
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction .pos (some (.inl ⟨i + 1, by omega⟩))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, hm, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state =
          some (.inl ⟨i + 1, by omega⟩) := by rw [hstep]; rfl
      have hp' : ((ifEqTM w₀ u v).tm.step cfg).inputPos.val = (i + 1) + 1 := by
        rw [hstep]
        change (moveInputPos cfg.inputPos .pos).val = i + 1 + 1
        rw [moveInputPos_pos_of_ne_right _ (by omega)]
        simp only
        omega
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hprefix' : x.take (i + 1) = w₀.take (i + 1) := by
        rw [List.take_succ, List.take_succ, hprefix, hm, List.getElem?_eq_getElem hi]
      obtain ⟨t, ht, htstate, htout⟩ := ih (i + 1) (by omega) (by omega) hprefix'
        ((ifEqTM w₀ u v).tm.step cfg) hs' hp' ho'
      refine ⟨t + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      exact ⟨htstate, htout⟩
    · have he : x ≠ w₀ := by
        intro he
        subst x
        exact hm (List.getElem?_eq_getElem hi)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, if_neg hm]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf

/-- Testing equality with a fixed string is computable in linear time: for any fixed
`w₀ u v`, the function `w ↦ u` if `w = w₀` and `w ↦ v` otherwise. (Instantiated by
the `HALT` reduction as the postprocessor `w ↦ if w = [true] then [false] else
[true]`; see `TCSlib.Complexity.Uncomputability.Halting`.)

**Proof sketch.** Hardcode `w₀`, `u`, and `v` in the states. The machine walks the
input left to right comparing it against `w₀` symbol by symbol (`|w₀| + 1`
comparison states); on the first mismatch — including the input ending early (blank
read) or running long (a symbol where `w₀` is exhausted) — it switches to an
emission chain for `v`, and after matching all of `w₀` and then reading the boundary
blank it switches to an emission chain for `u` (at most `|u| + |v| + 2` further
states, one emitted symbol per step). Every run halts within
`|w₀| + max |u| |v| + 3` steps — a constant, absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_ifEq (w₀ u v : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1) := by
  refine ⟨ifEqTM w₀ u v, w₀.length + max u.length v.length + 3, fun x => ?_⟩
  obtain ⟨t, ht, hs, ho⟩ := ifEq_run w₀ u v x w₀.length 0 (by omega) (by omega) rfl
    ((ifEqTM w₀ u v).tm.initCfg x) rfl (by simp) rfl
  have hbase : (ifEqTM w₀ u v).ComputesInTime x (if x = w₀ then u else v) t :=
    ⟨_, hs, ho, rfl⟩
  exact hbase.mono (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`.

**Implementation note (epoch 2).** The shared `bufferedCompTM` has
`M₁.k + (1 + M₂.k)` tapes and uses one physical step per simulated step.
The first halting time is at most `T₁ |x|`; rewind and dispatch take exactly
`|f x| + 2` steps, including the unconditional first left move. Consequently
`2 * T₁ |x| + T₂ (T₁ |x|) + 2` suffices, and the theorem uses `c = 2`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  refine ⟨bufferedCompTM M₁ M₂, 2, fun x => ?_⟩
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M₁ M₂ x (f x) (T₁ x.length) (h₁ x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((computesInTime_iff _ _ _ _).mp (h₁ x)).2
    simpa only [ho] using M₁.tm.output_length_le x (T₁ x.length)
  -- This is the only use of monotonicity: transfer the intermediate length bound.
  have htime : T₂ (f x).length ≤ T₂ (T₁ x.length) := hT₂ hlen
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg (f x)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ (f x).length)
  have hc := (computesInTime_iff _ _ _ _).mp (h₂ (f x))
  have hbase : (bufferedCompTM M₁ M₂).ComputesInTime x (g (f x))
      (a + T₂ (f x).length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- **Partial (guarded) sequential composition** — the phase-4 API obligation
identified by the phase-3 audit (round 2, finding 10 and Argument F):
`Turing.FinTM.computesFunInTime_comp` requires both components to compute *total*
functions, so it cannot take a partially computing machine — such as the universal
evaluator — as a component. This lemma composes two arbitrary machines at the level
of their halting relations, with **no totality or time hypotheses**: `M` behaves on
`x` exactly as `M₂` behaves on `M₁`'s completed output — halting, completed outputs,
and divergence all correspond.

Statement notes. The intermediate string `y` is existentially quantified, but by
`Turing.FinTM.ComputesInTime.output_unique` at most one `y` satisfies the first
conjunct, so the right-hand side reads "`M₁` halts on `x` (necessarily with a unique
`y`), and then `M₂` halts on `y` with `w`". If `M₁` diverges on `x`, or halts but
`M₂` diverges on its output, both sides are empty — `M` diverges. A time-bounded
refinement is deliberately not stated; it will be added if and when a result needs
it.

**Proof sketch** (buffered intermediate output, per the audit's design). `M` carries
`M₁`'s and `M₂`'s work tapes plus a fresh *buffer* tape. Phase one simulates `M₁` on
the true input step for step, with each emission of `M₁` written to the buffer tape
(write, move right) instead of the output tape; the append-only output discipline
makes the buffer region a verbatim copy of `M₁`'s output, contiguous from the
initial head cell. If `M₁` never halts, neither does `M`. On `M₁`'s halting
transition, `M` rewinds the buffer head to the leftmost written cell — the head
rests on the blank immediately *right* of the written word, so the rewind's first
left move is unconditional (testing the current cell before moving would stop at the
wrong end; phase-4 audit, finding 3), then left while reading a symbol, then one
step right. Phase two simulates `M₂` with its *input-tape
reads served from the buffer*: the buffer holds exactly `y` with blank cells on both
sides, and `M` maintains `M₂`'s virtual input position on it, mirroring the clamped
input-head semantics of `Turing.moveInputPos` at both boundaries — the same
virtual-boundary emulation as the universal machine's sketch
(`TCSlib.Complexity.TuringMachine.Universal`); a blank read identifies a boundary,
and *which* boundary is determined by the direction of arrival, tracked in the
state — for an empty intermediate word the simulation starts with the right-boundary
tag already set, the left boundary one inward move away (phase-4 audit, finding 3).
`M₂`'s work-tape actions go to its own fresh tapes and its emissions to the
real output tape, untouched during phase one. `M` halts exactly when the simulated
`M₂` halts; step-for-step run correspondence in each phase gives both directions of
the iff.

**Implementation note (epoch 2).** The buffer and virtual-input invariants are
public in `Simulation.lean`. The arrival tag is constrained only at boundaries;
stationary moves preserve it, including suppressed outward moves. Dispatch always
sets it to true, which is already the right-boundary tag when the word is empty.
A simulated phase-one halt remains live through the exact `|y| + 2` rewind.
For the forward implication, phase-one divergence contradicts a completed run;
otherwise extend that completed run beyond the verified phase-two start using
absorbing halting, and recover the second completed computation by lockstep. -/
theorem exists_comp_partial (M₁ M₂ : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ y : List Bool,
          (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesInTime y w t := by
  classical
  refine ⟨bufferedCompTM M₁ M₂, fun x w => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    -- A divergent first component would keep every composite configuration live.
    have hh : ∃ s, (M₁.tm.runFrom (M₁.tm.initCfg x) s).state = none := by
      by_contra h
      have hr := bufferedFirstCfg_run M₁ M₂ (M₁.tm.initCfg x) t
        (fun s _ hs => h ⟨s, hs⟩)
      rw [← bufferedFirstCfg_init] at hr
      have hc := ((computesInTime_iff _ _ _ _).mp ht).1
      rw [hr] at hc
      simp only [bufferedFirstCfg, Option.some_ne_none] at hc
    obtain ⟨s, hs⟩ := hh
    let y := (M₁.tm.runFrom (M₁.tm.initCfg x) s).output
    have hy : M₁.ComputesInTime x y s := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hy
    -- Extend a completed run past the verified administrative prefix.
    have hc := (computesInTime_iff _ x w (a + t)).mp (ht.mono (by omega))
    rw [MultiTapeTM.runFrom_add, ha] at hc
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    rw [hr] at hc
    refine ⟨y, ⟨s, hy⟩, t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  · rintro ⟨y, ⟨s, hs⟩, ⟨t, ht⟩⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hs
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    have hc := (computesInTime_iff _ _ _ _).mp ht
    refine ⟨a + t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [MultiTapeTM.runFrom_add, ha, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩

/-- A finite controller runs `D` with its first emission captured in a register,
rewinds, then enters the selected branch on disjoint fresh tapes. A simulated halt
is represented by a live control state so that dispatch occurs only after `D` halts.
An empty register at dispatch halts safely. -/
private def condTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := D.k + (M₁.k + M₂.k)
  State := (Option D.State × Option Bool) ⊕ (Option Bool ⊕ (M₁.State ⊕ M₂.State))
  tm :=
    { q₀ := .inl (some D.tm.q₀, none)
      tr := fun q inp work => match q with
        | .inl (some q, reg) =>
          let a := D.tm.tr q inp (fun i => work (Fin.castAdd (M₁.k + M₂.k) i))
          ⟨a.inputTape, Fin.addCases a.workTapes (fun _ => (none, 0)), none,
            some (.inl (a.state, reg.or a.output))⟩
        | .inl (none, reg) => controlAction .neg (some (.inr (.inl reg)))
        | .inr (.inl reg) => match inp with
          | some _ => controlAction .neg (some (.inr (.inl reg)))
          | none => controlAction .pos
              (reg.map (fun b => .inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
        | .inr (.inr q) => rightAction D.k (fun s => .inr (.inr s))
            ((branchTM M₁ M₂ false).tm.tr q inp (fun i => work (Fin.natAdd D.k i))) }

/-- Embed a controller configuration with its output suppressed and the first
output symbol stored in the finite register. All branch tapes remain blank. -/
private def controlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) : Cfg (condTM D M₁ M₂).k Bool (condTM D M₁ M₂).State x where
  state := some (.inl (c.state, c.output.head?))
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes (fun _ _ => none)
  workTapePos := Fin.addCases c.workTapePos (fun _ => 0)
  output := []

/-- Before the simulated controller halts, one composite step exactly updates its
configuration and the first-emission register. The head-of-append identity makes
this invariant valid even without any assumption on the controller's output. -/
private lemma controlCfg_step (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (hs : c.state ≠ none) :
    (condTM D M₁ M₂).tm.step (controlCfg D M₁ M₂ c) =
      controlCfg D M₁ M₂ (D.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (controlCfg D M₁ M₂ c).state = some (.inl (some q, c.output.head?)) := by
      simp [controlCfg, hq]
    rw [hs']
    dsimp only [condTM]
    have hr : (fun i => (controlCfg D M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (M₁.k + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [controlCfg, Cfg.workTapeSymbols]
    have hi : (controlCfg D M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ ?_
    · simp [controlCfg, Action.apply, List.head?_append, Option.head?_toList]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · simp [controlCfg, Action.apply]

/-- Controller lockstep holds through its first halting step. Subsequent composite
steps perform the rewind, so no claim of lockstep after halting is made. -/
private lemma controlCfg_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (h : ∀ s, s < t → (D.tm.runFrom c s).state ≠ none) :
    (condTM D M₁ M₂).tm.runFrom (controlCfg D M₁ M₂ c) t =
      controlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      controlCfg_step D M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A completed singleton controller computation reaches the selected branch's
fresh initial configuration after a finite prefix.

**Proof sketch.** Choose the first halting time of `D` and use controller lockstep.
Output uniqueness identifies its completed output with `[b]`, so the register is
`some b`, including when that bit was emitted early. Rewind from the resulting
input position; the branch tapes and real output have remained untouched. -/
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
  classical
  obtain ⟨tD, hDc⟩ := hD
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨tD, ((computesInTime_iff D x [b] tD).mp hDc).1⟩
  let t := Nat.find hh
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x cf.output t :=
    (computesInTime_iff D x cf.output t).mpr ⟨hstop, rfl⟩
  have hout : cf.output = [b] := hc.output_unique hDc
  have hi : (condTM D M₁ M₂).tm.initCfg x = controlCfg D M₁ M₂ (D.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
  have hrun : (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
      controlCfg D M₁ M₂ cf := by
    rw [hi]
    exact controlCfg_run D M₁ M₂ (D.tm.initCfg x) t (fun s hs => Nat.find_min hh hs)
  obtain ⟨r, hr⟩ := rewind_from_any (condTM D M₁ M₂).tm
    (.inl (none, some b)) (.inr (.inl (some b)))
    (some (.inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (controlCfg D M₁ M₂ cf) (by simp [controlCfg, hstop, hout])
  refine ⟨t + r, cf.workTapes, cf.workTapePos, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun, hr]
  rfl

/-- **Branching on a decided predicate** — the second phase-4 combinator (phase-3
audit, round 2, Argument F, step 2 of the `HALT → UC` reduction): given a total
decider `D` for `p` and two branch machines, some machine behaves on every input
exactly as the branch selected by `p` does *on that same input*. The input tape is
read-only, so both branches see the original input.

**Proof sketch.** `D` computes the singleton output `[p x]` on every input, and
output is append-only, so along any run `D` emits exactly one symbol; simulate `D`
with that single emission recorded in a state register instead of emitted (no buffer
tape needed). On `D`'s halting transition, rewind the true input head to its initial
position: one step left, then left while reading a symbol, then one step right —
from any position this ends at input position `1`, the initial position, the clamp
at position `0` making the walk safe (including on empty input). Then transfer
control to a disjoint copy of `M₁` or `M₂` according to the register. The branches'
work tapes are fresh tapes `D` never touched, the output tape is untouched by phase
one, and the input head is back at its initial position, so the selected branch's
run is reproduced verbatim; determinism (`Turing.FinTM.ComputesInTime.output_unique`)
identifies `D`'s completed output with `[p x]`, so the selected branch is
`cond (p x) M₁ M₂`.

The implementation retains the first emission, with the exact invariant that the
register is the head of the simulated output. A live administrative state follows
the simulated halt before the first left move. For the forward implication, extend
any completed composite run beyond the verified branch-start prefix using absorbing
halting, then apply branch lockstep; the reverse implication concatenates that
prefix with the selected branch run. -/
theorem exists_cond (D M₁ M₂ : FinTM Bool) (p : List Bool → Bool)
    (hD : D.Computes fun x => [p x]) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t := by
  refine ⟨condTM D M₁ M₂, fun x w => ?_⟩
  obtain ⟨a, tapes, heads, ha⟩ := condTM_start D M₁ M₂ x (p x) (hD x)
  have hr (t : ℕ) :
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) (a + t) =
        rightCfg (fun q => .inr (.inr q))
          ((branchTM M₁ M₂ (p x)).tm.runFrom ((branchTM M₁ M₂ (p x)).tm.initCfg x) t)
          tapes heads := by
    rw [MultiTapeTM.runFrom_add, ha]
    exact rightCfg_run (branchTM M₁ M₂ (p x)).tm (condTM D M₁ M₂).tm
      (fun q => .inr (.inr q)) (fun _ _ _ => rfl) _ tapes heads t
  constructor
  · rintro ⟨t, ht⟩
    have hc := (computesInTime_iff (condTM D M₁ M₂) x w (a + t)).mp
      (ht.mono (by omega))
    rw [hr t] at hc
    have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x w t :=
      (computesInTime_iff _ x w t).mpr
        ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
    exact ⟨t, (branchTM_computes M₁ M₂ (p x) x w t).mp hb⟩
  · rintro ⟨t, ht⟩
    have hb := (computesInTime_iff (branchTM M₁ M₂ (p x)) x w t).mp
      ((branchTM_computes M₁ M₂ (p x) x w t).mpr ht)
    refine ⟨a + t, (computesInTime_iff _ x w (a + t)).mpr ?_⟩
    rw [hr t]
    exact ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hb.1, hb.2⟩

end Turing.FinTM


## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim).
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing


## ===== TCSlib/Complexity/ClassNP/TMSAT.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.Universal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TMSAT: the first NP-complete language

[AB09, Theorem 2.9]: the language
`TMSAT = {⟨α, x, 1^n, 1^t⟩ : ∃ u ∈ {0,1}^n, M_α outputs 1 on ⟨x, u⟩ within t
steps}` is `NP`-complete — the "generic" `NP`-complete problem, read off the
definition of `NP` itself. This module defines `TMSAT` over the audited
Chapter-1 machine-code layer and states Theorem 2.9, together with the
polynomial time-constructibility statement the hardness reduction's unary
components rely on.

## Design and deviations from [AB09]

* **The tuple is right-nested `Turing.pairEncode`**:
  `⟨α, x, 1^n, 1^t⟩` is rendered
  `pairEncode α (pairEncode x (pairEncode 1^n 1^t))`, with `1^k` the string
  `List.replicate k true`. The pairing is self-delimiting and injective
  (`Turing.pairEncode_injective`), so the four components are recoverable and
  unique — strings not of this shape are simply not members.
* **"`M_α` outputs `1` on input `⟨x, u⟩` within `t` steps"** is rendered
  `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t` — completed
  output exactly `[true]` by step `t` (halting is absorbing), the audited
  output-convention of the whole development, against the total decoding of a
  `Turing.MachineCode`. The unary components make `n` and `t` at most the
  input length — [AB09]'s footnote 2: padding the input is what entitles the
  verifier and the reduction to run in time polynomial in `n` and `t`.
* **The generality split refines the audited `HALT` treatment**
  (`Complexity.HALT_NPHard` at `Turing.MachineCode`,
  `Complexity.HALT_not_mem_NP` at `Turing.EffectiveMachineCode`): the language
  and its `NP`-hardness need only a lawful code (`decode` totality and
  `decode_encode`; the reduction writes a *fixed* code string), while
  membership in `NP` runs the universal machine over an input-supplied `α` and
  therefore takes an effective scheme **with a polynomially bounded canonizer**
  — the hypothesis `Complexity.PolyBound c.canonizerTime` on the membership
  and completeness statements. Effectivity alone is **not** enough (round-1
  audit, finding 1, Argument A): `Turing.EffectiveMachineCode` bounds the
  canonizer's computability, not its cost, and a lawful effective scheme can
  plant arbitrarily expensive decidable information behind short codes,
  pushing its `TMSAT` outside `EXP ⊇ NP`. `NP`-completeness carries the same
  hypothesis.
* **`Complexity.timeConstructible_poly` is a new statement about a Chapter-1
  notion** (`Complexity.TimeConstructible`, `ClassP/TimeConstructible.lean`) —
  stated here rather than by editing the frozen audited file, and **flagged for
  this phase's audit** exactly as `Complexity.compl_mem_P` was in phase 1. The
  exponent is `c + 1` because time-constructibility requires `T n ≥ n`, which
  degree `0` would violate.

## Main definitions

* `Complexity.TMSAT` — [AB09, Theorem 2.9's language].

## Main results

* `Complexity.timeConstructible_poly` — `n ↦ C·(n+1)^(c+1)` is
  time-constructible (`C > 0`); the plan's supporting obligation for the
  reduction's unary components. [AB09, §1.3]
* `Complexity.timed_universal_quantitative` — the phase-3-mandated new public
  bridge with an explicit code-length coefficient; its proof is escalated
  under the epoch-2 brief's private-API protocol.
* `Complexity.TMSAT_mem_NP` — for schemes with polynomially bounded
  canonizers, the certificate is `u` itself; verification is timed universal
  simulation. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPHard` — the generic reduction: send `x` to
  `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPComplete` — [AB09, Theorem 2.9], under the same
  polynomial-canonizer hypothesis as membership.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.9 with footnote 2, pp. 43-44;
  §1.3 for time constructibility.)
-/

namespace Complexity

open Turing

/-- **The language `TMSAT`** [AB09, Theorem 2.9]: quadruples
`⟨α, x, 1^n, 1^t⟩` — right-nested `Turing.pairEncode`, unary third and fourth
components — such that some certificate `u` of length exactly `n` makes the
machine denoted by `α` (total decoding of the scheme `c`) halt on the paired
input `⟨x, u⟩` within `t` steps with completed output exactly `[true]`. -/
def TMSAT (c : MachineCode) : Language Bool :=
  {y | ∃ (α x u : List Bool) (n t : ℕ),
    y = pairEncode α
          (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) ∧
    u.length = n ∧
    (c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t}

/-! ### Exact unary polynomial generation

The following private machine enumerates a fixed-dimensional box of side
`|x| + 1`. Its output is a unary polynomial, so composing it with the public
linear-time binary length counter gives an exact binary polynomial value.
No private declaration from the Chapter-1 counter is used.
-/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive PolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance polyControlFintype (c C : ℕ) : Fintype (PolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance polyControlDecidableEq (c C : ℕ) : DecidableEq (PolyControl c C) :=
  (proxy_equiv% (PolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def polyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def polyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : PolyControl c C) : Action (c + 1) Bool (PolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def polyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := PolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then polyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then polyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else polyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then polyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def polyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => polyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma polyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (polyMove i d s').apply (polyCfg x q s h o) =
      polyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [polyMove, polyCfg, Action.apply, hj]
  · simp [polyMove, polyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma poly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      polyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        polyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma poly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      polyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, polyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [polyCfg] using polyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, polyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma poly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (polyUnaryTM c C).tm.step
      (polyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      polyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, polyUnaryTM, polyCfg, i.isLt, ↓reduceDIte]
  simpa [polyCfg] using polyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def polyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (polyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma poly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (polyCost q C i + 2) + q + 2) =
      polyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (polyUnaryTM c C).tm.runFrom
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (polyCost q C i + 2) =
        polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (polyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', polyCfg, Cfg.workTapeSymbols, polyTape, hj]
      have hs : (polyUnaryTM c C).tm.step (polyCfg x q (.loop ⟨i, hi⟩) h' o) =
          polyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [polyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) _ = _
        rw [show polyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [polyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) 1 =
            polyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          poly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (polyUnaryTM c C).tm.runFrom
            (polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (polyCost q C i) =
            polyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (polyCost q C (i - 1) + 2) + q + 2 =
              polyCost q C i := by
            calc
              _ = polyCost q C (i - 1 + 1) := rfl
              _ = polyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show polyCost q C i + 2 = 1 + polyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (polyUnaryTM c C).tm.step
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          polyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, Cfg.workTapeSymbols, polyCfg, Function.update_self,
          polyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, poly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (polyCost q C i + 2) + q + 2 =
          (polyCost q C i + 2) + (r * (polyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma polyTape_write (q : ℕ) :
    Function.update (polyTape q) (q : ℤ) (some true) = polyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [polyTape]
  · rw [Function.update_of_ne hz]
    unfold polyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma polyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    polyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [polyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      polyCost q C (r + 1) = q * (polyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def polyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => polyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma poly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x) i =
      polyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, polyCopyCfg, polyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (polyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [polyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact polyTape_write i
    · funext k
      simp [polyUnaryTM, polyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma poly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      polyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        polyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma poly_start (c C : ℕ) (x : List Bool) :
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (polyUnaryTM c C).tm.step
      (polyCopyCfg c C x x.length (le_refl _)) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (polyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [polyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact polyTape_write x.length
    · funext k
      simp [polyUnaryTM, polyCopyCfg, polyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', poly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact poly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary polynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma poly_unary_computes (c C : ℕ) :
    (polyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := poly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (polyUnaryTM c C).tm.runFrom
      (polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (polyCost (x.length + 1) C (c + 1)) =
      polyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [polyCost, hout] using hl
  have hbase : (polyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + polyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, poly_start, hloop]
    simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (polyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring

/-- **Polynomial bounds are time constructible**: for `C > 0`, the function
`n ↦ C·(n+1)^(c+1)` is `Complexity.TimeConstructible`. (A **new statement about
the Chapter-1 notion**, flagged for this phase's audit — see the deviations
list; the exponent `c + 1` keeps `T n ≥ n`, which degree `0` would violate.)
This is the plan's supporting obligation for the `TMSAT` reduction's unary
components.

**Proof sketch.** The bound `n ≤ n + 1 ≤ C·(n+1)^(c+1)` holds since `C ≥ 1`.
The machine: scan the input once, incrementing a little-endian binary counter
per cell to obtain `n` (the audited `Complexity.timeConstructible_id` fill is
the in-repo precedent; its private counter layer is a template, not a citable
API — phase-1 audit, finding 5); then compute `(n+1)^(c+1)` by `c + 1`
successive schoolbook binary multiplications and multiply by the constant `C`
(a fixed number of multiplications on operands of `O((c+1)·log(n+2) + log(C+1))`
bits, each polynomial in the bit length); emit the result as
`(T |x|).bits` (little-endian, the `Complexity.TimeConstructible` output
convention). Budget: the scan is `n` steps and the arithmetic polylogarithmic,
against the constant-slack budget `c'·(C·(n+1)^(c+1) + 1)` — ample.

**Implementation note (epoch 2).** The formal proof uses an exact unary
box-enumeration machine followed by the public linear-time binary length
counter, rather than formalizing schoolbook multiplication. Each of `c+1`
unary loop tapes has length `n+1`; each box point emits exactly `C` bits.
The generator costs at most `(C+5(c+1)+4)(n+1)^(c+1)`; timed composition with
`timeConstructible_id` preserves linear time in the polynomial's value.
This is a proof-route deviation only; the frozen statement is unchanged. -/
theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
    TimeConstructible fun n => C * (n + 1) ^ (c + 1) := by
  have hdom (n : ℕ) : (n + 1) ^ (c + 1) ≤ C * (n + 1) ^ (c + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((n + 1) ^ (c + 1)) hC
  refine ⟨fun n => ?_, ?_⟩
  · have hp : n + 1 ≤ (n + 1) ^ (c + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
        (show 1 ≤ c + 1 by omega)
    exact (Nat.le_succ n).trans (hp.trans (hdom n))
  · obtain ⟨_, a, ha, M, hM⟩ := timeConstructible_id
    have hcounter : M.ComputesFunInTime (fun x => x.length.bits) (fun n => a * (n + 1)) :=
      hM
    obtain ⟨N, b, hN⟩ := FinTM.computesFunInTime_comp (poly_unary_computes c C) hcounter
      (by intro m n h; exact Nat.mul_le_mul_left a (Nat.add_le_add_right h 1))
    let A := C + 5 * (c + 1) + 4
    refine ⟨(b + 1) * (a + 1) * (A + 1),
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _), N, ?_⟩
    intro x
    have hb := hN x
    simp only [Function.comp_apply, List.length_replicate] at hb
    apply hb.mono
    have hmajor : A * (x.length + 1) ^ (c + 1) + 1 ≤
        (A + 1) * (C * (x.length + 1) ^ (c + 1) + 1) := by
      have hm := Nat.mul_le_mul_left A (hdom x.length)
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    change b * (A * (x.length + 1) ^ (c + 1) +
        a * (A * (x.length + 1) ^ (c + 1) + 1) + 1) ≤ _
    calc
      _ = b * (a + 1) * (A * (x.length + 1) ^ (c + 1) + 1) := by ring
      _ ≤ (b + 1) * (a + 1) *
          ((A + 1) * (C * (x.length + 1) ^ (c + 1) + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (a + 1) (Nat.le_succ b)) hmajor
      _ = _ := by ring

/-! ### Quantitative timed-universal bridge -/

/-- The canonizer's completed serialization cannot be longer than its run. -/
private lemma tmsat_serialization_length (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)).2
  simpa only [hout] using c.canonizer.tm.output_length_le α (c.canonizerTime α.length)

/-- Flattening a nonempty word for each element cannot shorten a list. -/
private lemma tmsat_flatMap_length {A B : Type} (f : A → List B)
    (hf : ∀ a, 1 ≤ (f a).length) (l : List A) : l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hf a
    omega

/-- Every transition record contains at least its two-bit input-head action. -/
private lemma tmsat_action_nonempty {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    1 ≤ (actionBits a).length := by
  have hs : 2 ≤ (signBits a.inputTape).length := by
    cases a.inputTape <;> exact Nat.le_refl 2
  change 1 ≤ (signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state).length
  simp only [List.length_append]
  omega

/-- The canonical serialization bounds the bit-header length, initial-state
index, and total number of states.

**Proof sketch.** The header contains the first two fields. Each state has a
nonempty transition record in the serialized table, so its number of records
also bounds the state count. This uses the public serialization definition. -/
private lemma tmsat_serialization_parameters (M : CodeTM) :
    (Nat.bits M.numStates).length ≤ M.serialize.length ∧
      M.tm.q₀.val ≤ M.serialize.length ∧ M.numStates + 1 ≤ M.serialize.length := by
  let f := fun q : Fin (M.numStates + 1) =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)
  have hf (q : Fin (M.numStates + 1)) : 1 ≤ (f q).length := by
    dsimp only [f]
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    have := tmsat_action_nonempty (M.tm.tr q none (fun _ => none))
    omega
  have htable : M.numStates + 1 ≤ ((List.finRange (M.numStates + 1)).flatMap f).length := by
    simpa only [List.length_finRange] using tmsat_flatMap_length f hf
      (List.finRange (M.numStates + 1))
  have hlen : M.serialize.length = 2 * (Nat.bits M.numStates).length + 2 +
      (M.tm.q₀.val + 1 + ((List.finRange (M.numStates + 1)).flatMap f).length) := by
    change (pairEncode (Nat.bits M.numStates)
      ((List.replicate M.tm.q₀.val true ++ [false]) ++
        (List.finRange (M.numStates + 1)).flatMap f)).length = _
    simp only [universal_pair_length, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
  rw [hlen]
  omega

/-- The concrete coefficient displayed in the private timed-simulator proof
is bounded by the mandated public bridge's closed coefficient.

**Proof sketch.** The serialization, header length, initial index, and state
count are each bounded by the canonizer time. Expanding the concrete startup
and block coefficients gives one canonizer term plus thirteen such bounded
terms and constant fifty. This is solely an arithmetic bound on the displayed
expression, not a bound on `timed_universal`'s arbitrary existential witness. -/
private lemma tmsat_concrete_coefficient (c : EffectiveMachineCode) (α : List Bool) :
    3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14 ≤ 3 * α.length + 14 * c.canonizerTime α.length + 50 := by
  have hlen := tmsat_serialization_length c α
  obtain ⟨hbits, hstart, hstates⟩ := tmsat_serialization_parameters (c.decode α)
  unfold universalBlockBound
  omega

/-- A single timed simulator, selected before the code and input, preserves
both successful completion and timeout with the explicit budget
`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.

**The phase-3-mandated bridge statement: new public surface for the epoch-2
audit.** Its coefficient is the displayed function of the code length; no
bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.

**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
timed simulator's construction, bound the decoded serialization length by the
canonizer's output-time bound, and bound the state/header sizes by that
serialization. The existing proof's coefficient is then at most the displayed
coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
`Universal.lean` are private. The public API exposes only the existential
coefficient, so the construction cannot be reused through that API. This single
bridge declaration is intentionally admitted under the brief's escalation
protocol: the maintainer must export a quantitative concrete bounded-answer
lemma from Chapter 1 (including its timeout branch) and discharge this proof.
Chapter-1 sources are unchanged.

**Discharged (2026-10-03, maintainer serial merge).** Chapter 1 now exports
`Turing.timed_universal_concrete`: the concrete simulator's bounded-answer
theorem with the private startup expression expanded into public vocabulary
and both clauses preserved. This proof is that export, the arithmetic bound
`tmsat_concrete_coefficient` on its displayed coefficient, and
`Turing.FinTM.ComputesInTime.mono`. The escalation paragraph above is
retained as audit history; its final sentence described the pre-export
state, and the export is flagged for the shared infrastructure audit
round. -/
theorem timed_universal_quantitative (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  obtain ⟨hsucc, htimeout⟩ := hU α x t
  have hle : (3 * α.length + c.canonizerTime α.length +
      (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length +
      2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14) * (t + 1) ^ 2 ≤
      (3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (tmsat_concrete_coefficient c α)
  exact ⟨fun output hout => (hsucc output hout).mono hle,
    fun hnone => (htimeout hnone).mono hle⟩

/-- The exact success-tagged output or timeout answer of a bounded source run. -/
private def tmsatAnswer (c : MachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  let cfg := (c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t
  if cfg.state = none then true :: cfg.output else [false]

/-- Both clauses of the quantitative bridge yield a completed answer for every
well-formed timed request, including divergent source computations.

**Proof sketch.** Inspect the source configuration at the deadline. A halted
configuration witnesses completed computation with its full output. A live
configuration rules out every completed output, activating the timeout clause. -/
private lemma tmsat_simulator_total (c : EffectiveMachineCode) (U : FinTM Bool)
    (hU : ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool, (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)))
    (α x : List Bool) (t : ℕ) :
    U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (tmsatAnswer c.toMachineCode α x t)
      ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2) := by
  by_cases hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none
  · have hs := (FinTM.computesInTime_iff (c.decode α).toFinTM x
      (((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output) t).mpr ⟨hh, rfl⟩
    simpa only [tmsatAnswer, if_pos hh] using (hU α x t).1 _ hs
  · have hs : ∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t := by
      intro output ho
      exact hh ((FinTM.computesInTime_iff _ _ _ _).mp ho).1
    simpa only [tmsatAnswer, if_neg hh] using (hU α x t).2 hs

/-- Acceptance compares the entire captured answer with `[true,true]`;
timeouts and successful runs with any other completed output are rejected. -/
private lemma tmsatAnswer_accept (c : MachineCode) (α x : List Bool) (t : ℕ) :
    tmsatAnswer c α x t = [true, true] ↔
      (c.decode α).toFinTM.ComputesInTime x [true] t := by
  rw [FinTM.computesInTime_iff]
  dsimp only [tmsatAnswer]
  split <;> simp_all [CodeTM.toFinTM]

/-- The polynomial canonizer hypothesis gives one polynomial budget, uniform
over every code length and unary deadline bounded by the instance length.

**Proof sketch.** Bound both the linear code-length term and the canonizer
majorant by a power of degree `max 1 e`. Absorb the constant term into the
same positive power and multiply by the deadline's quadratic bound. No
monotonicity of the canonizer time itself is assumed. -/
private lemma tmsat_simulation_budget (c : EffectiveMachineCode)
    (hc : PolyBound c.canonizerTime) :
    ∃ A d : ℕ, ∀ m r t : ℕ, r ≤ m → t ≤ m →
      (3 * r + 14 * c.canonizerTime r + 50) * (t + 1) ^ 2 ≤ A * (m + 1) ^ d := by
  obtain ⟨C, e, he⟩ := hc
  refine ⟨3 + 14 * C + 50, max 1 e + 2, ?_⟩
  intro m r t hr ht
  have hp : 1 ≤ (m + 1) ^ max 1 e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hrp : r ≤ (m + 1) ^ max 1 e := by
    calc r ≤ m + 1 := by omega
      _ = (m + 1) ^ 1 := by simp
      _ ≤ (m + 1) ^ max 1 e := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_left _ _)
  have hH : c.canonizerTime r ≤ C * (m + 1) ^ max 1 e := by
    calc c.canonizerTime r ≤ C * (r + 1) ^ e := he r
      _ ≤ C * (m + 1) ^ e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e)
      _ ≤ C * (m + 1) ^ max 1 e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right _ _))
  have hcoef : 3 * r + 14 * c.canonizerTime r + 50 ≤
      (3 + 14 * C + 50) * (m + 1) ^ max 1 e := by
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  calc
    _ ≤ ((3 + 14 * C + 50) * (m + 1) ^ max 1 e) * (m + 1) ^ 2 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by rw [Nat.mul_assoc, ← Nat.pow_add]

/-- The right-nested quadruple used by `TMSAT`, with exact unary fields. -/
private def tmsatQuad (α x : List Bool) (n t : ℕ) : List Bool :=
  pairEncode α (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true)))

/-- All four tuple components fit inside the full encoded instance. -/
private lemma tmsat_quad_bounds (α x : List Bool) (n t : ℕ) :
    α.length ≤ (tmsatQuad α x n t).length ∧ x.length ≤ (tmsatQuad α x n t).length ∧
      n ≤ (tmsatQuad α x n t).length ∧ t ≤ (tmsatQuad α x n t).length := by
  simp only [tmsatQuad, universal_pair_length, List.length_replicate]
  omega

/-- The verifier specification uses an exact odd-length split, parses the
quadruple, and tests only the requested prefix of the padded certificate. -/
private def tmsatVerifier (c : MachineCode) : Language Bool :=
  {z | ∃ (y w α x : List Bool) (n t : ℕ),
    z = y ++ w ∧ w.length = y.length + 1 ∧ y = tmsatQuad α x n t ∧
      (c.decode α).toFinTM.ComputesInTime (pairEncode x (w.take n)) [true] t}

/-- Exact certificates force odd total length and recover the split position uniquely. -/
private lemma tmsat_split_length (y w : List Bool) (hw : w.length = y.length + 1) :
    (y ++ w).length % 2 = 1 ∧ ((y ++ w).length - 1) / 2 = y.length := by
  simp only [List.length_append, hw]
  omega

/-- The exact `m+1`-bit certificate convention is equivalent to the language's
original `n`-bit witness. No certificate-length majorization changes the source run.

**Proof sketch.** Pad the original witness with false bits and recover it by
taking its first `n` bits. Conversely, equality of the two concatenations and
their exact certificate lengths forces equal split positions, so the accepted
prefix has length exactly `n`. The tuple's unary field bounds `n` by `m`. -/
private lemma tmsat_certificate_equiv (c : MachineCode) (y : List Bool) :
    y ∈ TMSAT c ↔ ∃ w : List Bool, w.length = y.length + 1 ∧ y ++ w ∈ tmsatVerifier c := by
  constructor
  · rintro ⟨α, x, u, n, t, hy, hu, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    let w := u ++ List.replicate (y.length + 1 - n) false
    have hw : w.length = y.length + 1 := by
      simp only [w, List.length_append, List.length_replicate, hu]
      omega
    refine ⟨w, hw, y, w, α, x, n, t, rfl, hw, hy, ?_⟩
    have htake : w.take n = u := List.take_left' hu
    rw [htake]
    exact hs
  · rintro ⟨w, hw, y', w', α, x, n, t, he, hw', hy, hs⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, hw, hw'] at hlen
    obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
    refine ⟨α, x, w.take n, n, t, hy, ?_, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    rw [List.length_take, Nat.min_eq_left (by omega : n ≤ w.length)]

/-- Timed buffered composition needs the second machine to terminate only on
the first machine's image. Its bound is measured against the original input.

**Proof sketch.** Capture the preprocessing output on the composition buffer,
rewind and dispatch through the public `bufferedComp_start` theorem, then
relocate the second run through `bufferedSecondCfg_run`. Output length is at
most preprocessing time, so capture and rewind cost at most twice that time
plus two. This also permits a timed universal machine that is partial on
malformed requests, provided preprocessing always constructs a valid request. -/
private lemma tmsat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
  intro x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- **`TMSAT ∈ NP` for polynomially canonizable schemes** [AB09, Theorem 2.9,
membership]: the certificate is `u` itself, and verification is timed
universal simulation. The hypothesis `Complexity.PolyBound c.canonizerTime`
is **load-bearing and cannot be dropped** (round-1 audit, finding 1,
Argument A): `Turing.EffectiveMachineCode` constrains the canonizer's
*computability*, not its cost, and there is a lawful effective scheme — the
base scheme behind a one-bit tag, with the tagged branch decoding `[1] ++ z`
to a one-step machine that outputs the bit `A z` of a decidable language
`A ∉ EXP` — whose `TMSAT` decides `A` on the trivial instances
`⟨[1] ++ z, [], 1^0, 1^1⟩`; membership in `NP ⊆ EXP` would contradict
`A ∉ EXP`. The polynomial canonizer bound is what restores a uniform
simulation budget.

**Proof sketch.** Certificate parameters `(1, 1)`: length exactly `m + 1` on
inputs of length `m` (the declared `n` satisfies `n ≤ m`, since `1^n` sits
inside `y`; the certificate is `u` padded to `m + 1` bits, `u` recovered as the
first `n` bits — no marker needed, `n` is read off `y`). The verifier language:
`V = {y ++ w : |w| = |y| + 1`, `y` parses as a quadruple
`⟨α, x, 1^n, 1^t⟩`, and the machine `α` denotes accepts `⟨x, w.take n⟩` within
`t` steps`}`. `V ∈ P` by a machine with the named fill obligations: (i)
unique-split recovery — a well-formed input has length `m + (m + 1) = 2m + 1`,
**odd**, so the machine **rejects even lengths** and splits an odd length `N`
at `(N − 1) / 2` (round-1 audit, finding 4, correcting the drafted parity);
(ii) the **quadruple parser** — three nested `pairDecode` passes (the aligned
two-bit grammar; the `UniversalStartup` parsing layer is the in-repo
precedent) plus all-`true` shape checks on the third and fourth components,
rejecting any failure; (iii) **unary-to-binary clock conversion**:
`Turing.timed_universal`'s clock input is `Nat.bits t`, so the verifier
converts the unary `1^t` by counter increments (`Nat.bits 0 = []` at the
`t = 0` edge, where every instance is negative —
`Turing.FinTM.not_computesInTime_zero`); (iv) **assembly and relocated
simulation**: build `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x
(w.take n))` on a work tape and run the timed universal machine `U` of
`Turing.timed_universal c` relocated-and-captured (the standing obligations);
`U` answers `true :: output` or `[false]` by design and its branches are
exhaustive, so acceptance is exactly the complete captured answer
`[true, true]` — a timeout, or any completed output other than `[true]`,
rejects; (v) the verdict with buffered output. **Budget** — where the
hypothesis enters: `U` completes within `C_α·(t+1)^2` steps, and the round-1
audit's inspection of the `Universal` module's bound definitions gives, with
`r = |α|` and `H = c.canonizerTime r`, the chain `C_α ≤ 3r + 14·H + 50` (the
decoded serialization's length `L` bounds the header/state parameters and is
itself at most `H`, the canonizer writing it within its time budget —
`Turing.MultiTapeTM.output_length_le`); `PolyBound c.canonizerTime` then
bounds `C_α` by a polynomial in `r ≤ m` uniformly, and with `t ≤ m` the whole
simulation is polynomial in `m`: `V ∈ P` via `Complexity.mem_P_of_dtime_le`.
**Named fill obligation (new public bridge)**: the public
`Turing.timed_universal` exposes its constant only existentially per code, so
the fill needs a quantitative public form of the bound (an addition to the
audited `Universal` surface, to be requested through the standing shared-file
mechanism and flagged for its audit round — the round-1 finding's repair
guidance; a prose obligation alone cannot discharge the budget). Membership
equivalence: forward, a `TMSAT` witness `u` pads to `m + 1` bits (absorbing
halting keeps the accepting run); backward, a certificate's first `n` bits are
a witness — `Turing.timed_universal`'s two branches convert between `U`'s
answers and `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t`
exactly, and `Turing.pairEncode_injective` pins the parsed components to the
defining existential's. -/
theorem TMSAT_mem_NP (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    TMSAT c.toMachineCode ∈ NP := by
  obtain ⟨U, hU⟩ := timed_universal_quantitative c
  obtain ⟨A, d, hbudget⟩ := tmsat_simulation_budget c hc
  have htotal := tmsat_simulator_total c U hU
  have hV : tmsatVerifier c.toMachineCode ∈ P := by
    -- CONTINUATION D-MEM: construct the odd-split/quadruple parser and unary
    -- clock converter, returning a well-formed zero-deadline request on failure.
    -- Compose its output with `htotal` through `tmsat_comp_on_image`, use
    -- `hbudget` and `tmsat_quad_bounds`, and compare the entire captured answer
    -- with `[true,true]` using `tmsatAnswer_accept`. No totality of U on malformed
    -- strings may be assumed. This is a partial-delivery admission, not a
    -- discharge of the verifier-machine obligation.
    sorry
  refine ⟨1, 1, tmsatVerifier c.toMachineCode, hV, ?_⟩
  intro y
  simpa only [Nat.pow_one, Nat.one_mul] using tmsat_certificate_equiv c.toMachineCode y

/-- The audited deadline formula majorizes the normalized wrapper runtime.
The certificate length remains exactly `C*(n+1)^c` throughout this inequality.

**Proof sketch.** The paired input plus one cell is bounded by
`(C+3)(n+1)^max(1,c)`. Raise to the wrapper degree, absorb its additive one
into the positive power, and square for the one-work-tape normalization.
Only the deadline is enlarged. -/
private lemma tmsat_deadline_bound (K B e C c n : ℕ) :
    K * (B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1) ^ 2 ≤
      ((K + 1) * (B + 1) ^ 2 * (C + 3) ^ (2 * e)) *
        (n + 1) ^ (2 * e * max 1 c) := by
  have hlin : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left 1 c)
  have hpow : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right 1 c)
  have hsize : 2 * n + 2 + C * (n + 1) ^ c + 1 ≤
      (C + 3) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hpow
    rw [Nat.add_mul]
    omega
  have hepow : (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e ≤
      (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ ((C + 3) * (n + 1) ^ max 1 c) ^ e := Nat.pow_le_pow_left hsize e
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) e]
  have hpos : 1 ≤ (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.succ_pos _))
  have hinner : B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1 ≤
      (B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ B * ((C + 3) ^ e * (n + 1) ^ (e * max 1 c)) +
          (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
        Nat.add_le_add (Nat.mul_le_mul_left B hepow) hpos
      _ = _ := by ring
  calc
    _ ≤ (K + 1) * ((B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hinner 2)
    _ = _ := by
      simp only [Nat.mul_pow, ← Nat.pow_mul]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Constant strings are polynomial-time computable by finite emission chains. -/
private lemma tmsat_constant_poly (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_const w
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- The exact binary certificate length is polynomial-time computable,
including zero coefficients and degree zero.

**Proof sketch.** Follow the audited three-way split: coefficient zero emits
the empty word; positive coefficient and degree zero emits its fixed binary
representation from finite control; positive coefficient and positive degree
uses `timeConstructible_poly C (c-1)`. Only the runtime is enlarged. -/
private lemma tmsat_exact_certificate_bits (C c : ℕ) :
    PolyTimeComputable (fun x : List Bool => (C * (x.length + 1) ^ c).bits) := by
  by_cases hC : C = 0
  · simpa [hC] using tmsat_constant_poly []
  · by_cases hc : c = 0
    · simpa [hc] using tmsat_constant_poly C.bits
    · obtain ⟨_, a, _, M, hM⟩ := timeConstructible_poly C (c - 1) (by omega)
      have he : c - 1 + 1 = c := by omega
      simp only [he] at hM
      refine ⟨M, a * (C + 1), c, fun x => (hM x).mono ?_⟩
      have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
      calc
        _ ≤ a * ((C + 1) * (x.length + 1) ^ c) :=
          Nat.mul_le_mul_left a (by rw [Nat.add_mul, Nat.one_mul]; omega)
        _ = _ := by ring

/-- The wrapper's total output function rejects malformed pairs and otherwise
forwards the verifier's verdict on the concatenated components. -/
private noncomputable def tmsatWrapperOutput (V : Language Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | none => [false]
  | some (x, u) => [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)]

/-- Three applications of pairing injectivity pin every quadruple component;
unary equality pins the two natural-number fields by taking lengths. -/
private lemma tmsat_quad_injective (α x : List Bool) (n t : ℕ)
    (β y : List Bool) (m s : ℕ) (he : tmsatQuad α x n t = tmsatQuad β y m s) :
    α = β ∧ x = y ∧ n = m ∧ t = s := by
  have h₁ : (α, pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) =
      (β, pairEncode y (pairEncode (List.replicate m true) (List.replicate s true))) :=
    pairEncode_injective he
  obtain ⟨hα, hrest⟩ := Prod.mk.inj h₁
  have h₂ : (x, pairEncode (List.replicate n true) (List.replicate t true)) =
      (y, pairEncode (List.replicate m true) (List.replicate s true)) :=
    pairEncode_injective hrest
  obtain ⟨hx, hlast⟩ := Prod.mk.inj h₂
  have h₃ : (List.replicate n true, List.replicate t true) =
      (List.replicate m true, List.replicate s true) := pairEncode_injective hlast
  obtain ⟨hn, ht⟩ := Prod.mk.inj h₃
  refine ⟨hα, hx, ?_, ?_⟩
  · simpa only [List.length_replicate] using congrArg List.length hn
  · simpa only [List.length_replicate] using congrArg List.length ht

/-- Given a fixed coded wrapper with the prescribed deadline, the reduction
has exactly the original NP language as its preimage.

**Proof sketch.** Forward, use the original exact-length certificate and the
wrapper's accepting verdict. Backward, nested pairing injectivity forces the
code, input, certificate length, and deadline to be precisely the emitted ones.
Completed-output uniqueness then identifies acceptance with the verifier's
verdict, even if the chosen deadline exceeds the actual halting time. -/
private lemma tmsat_reduction_correct (c : MachineCode) (L V : Language Bool)
    (C e : ℕ) (α : List Bool) (T : ℕ → ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V)
    (hM : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ e →
      (c.decode α).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T x.length)) :
    ∀ x : List Bool, x ∈ L ↔ tmsatQuad α x (C * (x.length + 1) ^ e) (T x.length) ∈ TMSAT c := by
  classical
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu, hv⟩ := (hL x).mp hx
    refine ⟨α, x, u, C * (x.length + 1) ^ e, T x.length, rfl, hu, ?_⟩
    simpa only [MultiTapeTM.indicator, if_pos hv] using hM x u hu
  · rintro ⟨β, y, u, n, t, he, hu, hs⟩
    obtain ⟨rfl, rfl, hn, ht⟩ := tmsat_quad_injective α x
      (C * (x.length + 1) ^ e) (T x.length) β y n t he
    rw [← hn] at hu
    rw [← ht] at hs
    refine (hL _).mpr ⟨u, hu, ?_⟩
    have ho := hs.output_unique (hM _ u hu)
    by_contra hv
    simp [MultiTapeTM.indicator, hv] at ho

/-- **`TMSAT` is `NP`-hard** [AB09, Theorem 2.9, hardness]: the generic
reduction — for `L ∈ NP`, send `x` to `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`.

**Proof sketch.** Let `L ∈ NP` with parameters `(C₀, c₀, V)` and certificate
length `Q n = C₀·(n+1)^(c₀)`, and, via `Complexity.mem_P_iff`, a machine `M_V`
deciding `V` within `A·(m+1)^d`. **The encoded machine**: a wrapper `M'` that,
on input `z`, parses `z` as `Turing.pairEncode x u` (the pairing parser
obligation; on non-pairs, output `[false]` — `M'` is total), assembles
`x ++ u`, and runs `M_V` relocated-and-captured, forwarding the verdict. `M'`
computes a total function within an explicit polynomial; normalize by the
audited chain `Turing.FinTM.one_work_tape_binary` (its total-function
hypothesis holds) and `Turing.exists_codeTM`, and let `α₀ := c.encode M''` be
the resulting **fixed code string** (this is why plain `Turing.MachineCode`
suffices — the audited `Complexity.HALT_NPHard` recipe). Let
`T' n` the **explicit** deadline formula below. **The reduction map**
`f x := pairEncode α₀ (pairEncode x (pairEncode 1^{Q |x|} 1^{T' |x|}))`.
`Complexity.PolyTimeComputable f` by the named obligations: emit the doubled
fixed string `α₀` from finite control (emission chains), double-and-copy `x`,
and write the two unary runs by binary countdown, under the **exact-value
discipline** of the round-1 audit (finding 3): the certificate length `Q` must
be emitted **exactly** — majorizing it changes the language (at
`C₀ = c₀ = 0` and `L = V = {[true]}`, replacing `Q = 0` by `n + 1` flips the
empty input's membership) — by cases: `C₀ = 0` emits the empty run;
`C₀ > 0, c₀ = 0` emits the fixed constant `C₀` from finite control;
`C₀ > 0, c₀ > 0` computes the exact binary value by
`Complexity.timeConstructible_poly C₀ (c₀ - 1)`. The **deadline may be
majorized** (enlarging `t` only relaxes the budget of a total machine whose
verdict is fixed): with a wrapper bound `B·(s+1)^e` (`B, e ≥ 1`) on inputs of
length `s`, normalization multiplier `K`, and `s = 2n + 2 + Q n` on the
relevant inputs, take the audit's formula — `r := max 1 c₀`,
`D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`; then
`s + 1 ≤ (C₀+3)·(n+1)^r` gives `K·(B·(s+1)^e + 1)^2 ≤ T' n` at every `n`, and
`Complexity.timeConstructible_poly D (2er - 1)` computes `T'`'s exact binary
value (`2er ≥ 1`). Output length: `|f x| = 2|α₀| + 2|x| + 2·Q |x| + T' |x| +
6`, an explicit polynomial. **Correctness**: `f x ∈ TMSAT c` iff — by
`Turing.pairEncode_injective`, which pins the quadruple's components — some
`u` with `|u| = Q n` has `M''.toFinTM.ComputesInTime (pairEncode x u) [true]
(T' n)`; by `M''`'s semantics and budget this holds iff `x ++ u ∈ V` (the
wrapper's verdict is the `V`-indicator, completed outputs are unique —
`Turing.FinTM.ComputesInTime.output_unique`), and the `NP` membership
equivalence for `L` turns "some such `u`" into `x ∈ L`. Conclude
`Complexity.NPHard` by the definition, one reduction per `L ∈ NP`. -/
theorem TMSAT_NPHard (c : MachineCode) : NPHard (TMSAT c) := by
  classical
  intro L hL
  obtain ⟨C₀, c₀, V, hV, hL⟩ := hL
  obtain ⟨A, d, M_V, hM_V⟩ := mem_P_iff.mp hV
  have hwrap : ∃ (W : FinTM Bool) (B e : ℕ), 0 < B ∧ 0 < e ∧
      W.ComputesFunInTime (tmsatWrapperOutput V) (fun s => B * (s + 1) ^ e) := by
    -- CONTINUATION D-WRAP: implement the total aligned pairing parser;
    -- reject non-pairs, assemble x ++ u on a buffer, and relocate/capture M_V.
    -- `tmsat_comp_on_image` supplies the timed simulation composition.
    -- The remaining obligation is a concrete polynomial-time pair-to-concat
    -- preprocessing machine and its malformed-input branch.
    sorry
  obtain ⟨W, B, e, hB, he, hW⟩ := hwrap
  obtain ⟨M₁, K, hk, h₁⟩ := FinTM.one_work_tape_binary W (tmsatWrapperOutput V)
    (fun s => B * (s + 1) ^ e) hW
  obtain ⟨M'', hcode⟩ := exists_codeTM M₁ hk
  let α₀ := c.encode M''
  let r := max 1 c₀
  let D := (K + 1) * (B + 1) ^ 2 * (C₀ + 3) ^ (2 * e)
  let T' := fun n => D * (n + 1) ^ (2 * e * r)
  have hD : 0 < D :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.succ_pos _)))
      (Nat.pow_pos (by omega))
  have hexp : 1 ≤ 2 * e * r := by
    have hr : 0 < r := Nat.le_max_left 1 c₀
    have her := Nat.mul_pos he hr
    rw [Nat.mul_assoc]
    omega
  have hdeadline : TimeConstructible T' := by
    have h := timeConstructible_poly D (2 * e * r - 1) hD
    have heq : 2 * e * r - 1 + 1 = 2 * e * r := by omega
    simpa only [heq] using h
  have hcertificate := tmsat_exact_certificate_bits C₀ c₀
  have hnormalized (x u : List Bool) (hu : u.length = C₀ * (x.length + 1) ^ c₀) :
      (c.decode α₀).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T' x.length) := by
    have hrun := (hcode (pairEncode x u) (tmsatWrapperOutput V (pairEncode x u)) _).2
      (h₁ (pairEncode x u))
    simp only [tmsatWrapperOutput, pairDecode_pairEncode] at hrun
    rw [show c.decode α₀ = M'' from c.decode_encode M'']
    apply hrun.mono
    simpa only [universal_pair_length, hu] using tmsat_deadline_bound K B e C₀ c₀ x.length
  have hemit : PolyTimeComputable
      (fun x => tmsatQuad α₀ x (C₀ * (x.length + 1) ^ c₀) (T' x.length)) := by
    -- CONTINUATION D-EMIT: emit the fixed code and doubled input, then the
    -- exact unary certificate and deadline via binary countdown. The exact
    -- binary certificate is supplied by `hcertificate` (all three edge cases)
    -- and the exact binary deadline by `hdeadline`. Compose these submachines
    -- while retaining x, and prove the stated right-nested pairing layout.
    sorry
  exact ⟨_, hemit, tmsat_reduction_correct c L V C₀ c₀ α₀ T' hL hnormalized⟩

/-- **Theorem 2.9** [AB09]: `TMSAT` is `NP`-complete — over an effective
scheme with a polynomially bounded canonizer, the hypothesis its membership
half requires and cannot drop (round-1 audit, findings 1-2: without it, the
Argument-A scheme's `TMSAT` is `NP`-hard yet outside `NP`, so the completeness
conjunction fails).

**Proof sketch.** `Complexity.TMSAT_mem_NP` (with the same hypothesis `hc`)
and `Complexity.TMSAT_NPHard` at `c.toMachineCode`, assembled by the
definition of `Complexity.NPComplete`. -/
theorem TMSAT_NPComplete (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    NPComplete (TMSAT c.toMachineCode) := by
  exact ⟨TMSAT_mem_NP c hc, TMSAT_NPHard c.toMachineCode⟩

end Complexity


## ===== TCSlib/Complexity/ClassNP/NP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class NP

[AB09, §2.1, Definition 2.1]: a language `L` is in `NP` when membership has
polynomial-length certificates verifiable in polynomial time — `x ∈ L` iff some
certificate `u` of the prescribed polynomial length makes the verifier accept.

## Design and deviations from [AB09]

* **The certificate length is an explicit polynomial formula**, exactly
  `C · (|x| + 1)^c` bits: the definition quantifies over the *coefficient and
  degree*, not over an abstract length function. This is the phase-1 audit's
  repair (findings 1-2, Argument A): a length function constrained only by a
  numerical bound can itself smuggle undecidable information through length
  arithmetic — certificate *content* never enters — putting every
  length-determined language in the class. An explicit formula is computable,
  monotone, and information-free by construction. The numerical helper
  `Complexity.PolyBound` survives for bound bookkeeping only; it never appears
  in a class definition.
* **The verifier is a language, not a machine.** We render "polynomial-time TM
  `M` with `M(x, u) = 1`" as membership of the concatenation `x ++ u` in a
  verifier language `V ∈ P` — reusing the audited Chapter-1 class. The phase-1
  audit certified this abstraction sound (finding 10): `V ∈ P` supplies one
  uniform total decider, and for a fixed length formula, `V`'s values off the
  constrained strings change no membership statement.
* **Pairing is concatenation in the exact-length form** ([AB09], footnote 4):
  the definition never splits `x ++ u` — the membership equivalence quantifies
  over `x` and `u` separately, and with the explicit formula, any consumer
  that must recover the split can (`n + n·formula` arithmetic is computable
  and `n ↦ n + C(n+1)^c` is strictly increasing). The **bounded-length**
  variant ([AB09, Exercise 2.1]) is different: with `∃ u, |u| ≤ …` and plain
  concatenation, the empty certificate forces `V ⊆ L`, which collapses every
  prefix-free language to its verifier (audit finding 2, Argument B) — so the
  bounded form below pairs its inputs with the audited self-delimiting
  `Turing.pairEncode` instead.
* **Certificates have length exactly `C(|x|+1)^c`** (Definition 2.1 verbatim,
  with the formula for [AB09]'s "polynomial `p`").

## Main definitions

* `Complexity.NP` — the class NP. [AB09, Definition 2.1]

## Main results

* `Complexity.P_subset_NP` — `P ⊆ NP` (empty certificates). [AB09, §2.1]
* `Complexity.mem_NP_iff_exists_length_le` — bounded-length *paired*
  certificates define the same class. [AB09, Exercise 2.1, repaired per the
  phase-1 audit]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1, Definition 2.1, pp. 39-41;
  Exercise 2.1.)
-/

namespace Complexity

open Turing

/-- **The class NP** [AB09, Definition 2.1]: `L ∈ NP` iff there are a certificate
coefficient `C`, degree `c`, and a polynomial-time-decidable verifier language
`V ∈ P` such that `x ∈ L` exactly when some certificate `u` of length exactly
`C · (|x| + 1)^c` makes the concatenation `x ++ u` a member of `V`. The
certificate length is an explicit formula in `|x|` — never an abstract
function — so it is computable and carries no information beyond `|x|`
(phase-1 audit, finding 1). -/
def NP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ NP`** [AB09, §2.1, after Definition 2.1]: a language decidable in
polynomial time is verifiable with empty certificates.

**Proof sketch.** Take `C = 0` (certificate length `0 · (n+1)^0 = 0`) and
`V = L`: the only certificate of length `0` is `[]`, and `x ++ [] = x`, so the
membership equivalence is the identity. The audit confirmed this covers
`L = ∅`, `L = univ`, and `x = []` (finding table, question 2). -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, 0, L, hL, fun x => ?_⟩
  simp only [zero_mul, List.length_eq_zero_iff, exists_eq_left, List.append_nil]


/-- Remove the last `true` marker and the following false suffix. No marker
means failure, so stripping cannot cross the certificate boundary. -/
private def stripCertificate : List Bool → Option (List Bool)
  | [] => none
  | b :: v => match stripCertificate v with
    | some u => some (b :: u)
    | none => if b then some [] else none

/-- An all-false certificate region contains no marker. -/
private lemma stripCertificate_false (k : ℕ) :
    stripCertificate (List.replicate k false) = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, stripCertificate, ih]

/-- Stripping a padded certificate recovers the original certificate, including
the empty certificate and certificates that themselves contain `true`. -/
private lemma stripCertificate_pad (u : List Bool) (k : ℕ) :
    stripCertificate (u ++ true :: List.replicate k false) = some u := by
  induction u with
  | nil => simp [stripCertificate, stripCertificate_false]
  | cons b u ih => simp [stripCertificate, ih]

/-- Successful stripping identifies precisely the last-true decomposition.

**Proof sketch.** Induct from the right through the recursive call. A marker in
the tail survives, with the head prepended; otherwise the head must be `true`
and the tail must be all false. The simultaneous no-marker assertion supplies
that latter fact. -/
private lemma stripCertificate_spec (v : List Bool) :
    (stripCertificate v = none ↔ v = List.replicate v.length false) ∧
    (∀ u, stripCertificate v = some u ↔
      ∃ k, v = u ++ true :: List.replicate k false) := by
  induction v with
  | nil => simp [stripCertificate]
  | cons b v ih =>
    cases hv : stripCertificate v with
    | none =>
      have hfalse := ih.1.mp hv
      constructor
      · constructor
        · intro h
          cases b with
          | false => simpa [List.replicate_succ] using congrArg (false :: ·) hfalse
          | true => simp [stripCertificate, hv] at h
        · intro h
          rw [h]
          exact stripCertificate_false _
      · intro u
        constructor
        · intro h
          cases b with
          | false => simp [stripCertificate, hv] at h
          | true =>
            have hu : u = [] := by simpa [stripCertificate, hv] using h.symm
            subst u
            exact ⟨v.length, by simpa using congrArg (true :: ·) hfalse⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j
    | some w =>
      obtain ⟨k, hk⟩ := (ih.2 w).mp hv
      constructor
      · constructor
        · simp [stripCertificate, hv]
        · intro heq
          have : stripCertificate (b :: v) = none := by
            rw [heq]; exact stripCertificate_false _
          simp [stripCertificate, hv] at this
      · intro u
        constructor
        · intro h
          have hu : b :: w = u := by simpa [stripCertificate, hv] using h
          subst u
          exact ⟨k, by simp [hk]⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j

/-- The padded total length is strictly increasing, even at degree zero. -/
private lemma certificateTotal_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + (C + 1) * (n + 1) ^ c) := by
  intro m n h
  dsimp only
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_of_lt h) 1) c
  have hmul := Nat.mul_le_mul_left (C + 1) hpow
  omega

/-- The repaired exact width leaves room for the mandatory marker. -/
private lemma certificate_room (C c n : ℕ) :
    C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ c := by
  have h := Nat.one_le_pow c (n + 1) (Nat.succ_pos n)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Bounded search for the unique legal split. Failure remains `none`. -/
private def certificateSplit (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? fun n => n + (C + 1) * (n + 1) ^ c == m

/-- The bounded search succeeds exactly at a solution of the length equation.

**Proof sketch.** Any solution is at most the total length, hence lies in the
search range. A failed search would reject that very solution; a successful
search returns a solution, and strict monotonicity makes it unique. -/
private lemma certificateSplit_spec (C c m n : ℕ) :
    certificateSplit C c m = some n ↔ n + (C + 1) * (n + 1) ^ c = m := by
  constructor
  · intro h
    have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) h
    simpa only [beq_iff_eq] using hh
  · intro h
    have hn : n ∈ List.range (m + 1) := by simp only [List.mem_range]; omega
    cases hs : certificateSplit C c m with
    | none =>
      have hf := (List.find?_eq_none.mp hs) n hn
      simp [h] at hf
    | some j =>
      have hj : j + (C + 1) * (j + 1) ^ c = m :=
        by
          have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) hs
          simpa only [beq_iff_eq] using hh
      have : j = n := (certificateTotal_strictMono C c).injective (hj.trans h.symm)
      simp [this]

/-- In particular the empty input has no legal split. -/
private lemma certificateSplit_zero (C c : ℕ) : certificateSplit C c 0 = none := by
  cases h : certificateSplit C c 0 with
  | none => rfl
  | some n =>
    have hn := (certificateSplit_spec C c 0 n).mp h
    have hr := certificate_room C c n
    omega

/-- The forward verifier parses the audited pairing, enforces the original
exact width, and consults the old verifier on the concatenated word. -/
private def pairedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ x u, pairDecode y = some (x, u) ∧
    u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- On an encoded pair, the forward verifier imposes exactly the prescribed
length test and the old verification condition. -/
private lemma pairedVerifier_pair (C c : ℕ) (V : Language Bool) (x u : List Bool) :
    pairEncode x u ∈ pairedVerifier C c V ↔
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := by
  change (∃ a b, pairDecode (pairEncode x u) = some (a, b) ∧
    b.length = C * (a.length + 1) ^ c ∧ a ++ b ∈ V) ↔ _
  simp [pairDecode_pairEncode]

/-- A malformed pair is rejected before consulting the old verifier. -/
private lemma pairedVerifier_malformed (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : pairDecode y = none) : y ∉ pairedVerifier C c V := by
  rintro ⟨x, u, hp, -⟩
  rw [h] at hp
  cases hp

/-- The reverse verifier rejects a missing length split or marker, rechecks the
original bound after stripping, and consults the old paired verifier. -/
private def paddedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ n u, certificateSplit C c y.length = some n ∧
    stripCertificate (y.drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode (y.take n) u ∈ V}

/-- A missing solution of the length equation is rejection, not a default
split. In particular this covers the empty input by `certificateSplit_zero`. -/
private lemma paddedVerifier_no_split (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : certificateSplit C c y.length = none) : y ∉ paddedVerifier C c V := by
  rintro ⟨n, u, hn, -⟩
  rw [h] at hn
  cases hn

/-- For the prescribed exact width the search recovers precisely the input
boundary; no marker in the input can be mistaken for a certificate marker. -/
private lemma paddedVerifier_append (C c : ℕ) (V : Language Bool) (x v : List Bool)
    (hv : v.length = (C + 1) * (x.length + 1) ^ c) :
    x ++ v ∈ paddedVerifier C c V ↔ ∃ u, stripCertificate v = some u ∧
      u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  have hs : certificateSplit C c (x ++ v).length = some x.length := by
    apply (certificateSplit_spec _ _ _ _).mpr
    simp only [List.length_append, hv]
  change (∃ n u, certificateSplit C c (x ++ v).length = some n ∧
    stripCertificate ((x ++ v).drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode ((x ++ v).take n) u ∈ V) ↔ _
  rw [hs]
  simp

/-- An all-false region is rejected even when the input itself contains true
bits: the strip function is applied only after the recovered boundary. -/
private lemma paddedVerifier_no_marker (C c : ℕ) (V : Language Bool) (x : List Bool) :
    x ++ List.replicate ((C + 1) * (x.length + 1) ^ c) false ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ (List.length_replicate ..)]
  simp only [stripCertificate_false, reduceCtorEq, false_and, exists_false, not_false_eq_true]

/-- Even a correctly marked certificate that fits in the enlarged exact
region is rejected if its stripped witness exceeds the original bound. -/
private lemma paddedVerifier_too_long (C c : ℕ) (V : Language Bool) (x u : List Bool)
    (k : ℕ) (hv : (u ++ true :: List.replicate k false).length =
      (C + 1) * (x.length + 1) ^ c) (hu : C * (x.length + 1) ^ c < u.length) :
    x ++ (u ++ true :: List.replicate k false) ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ hv]
  rintro ⟨u', hs, hu', -⟩
  rw [stripCertificate_pad] at hs
  have he : u = u' := Option.some.inj hs
  subst u'
  exact Nat.not_le_of_lt hu hu'

/-- Padding and stripping give the exact witness equivalence; the runtime
obligations are separate from this purely semantic statement. -/
private lemma paddedVerifier_witness (C c : ℕ) (V : Language Bool) (x : List Bool) :
    (∃ v, v.length = (C + 1) * (x.length + 1) ^ c ∧ x ++ v ∈ paddedVerifier C c V) ↔
    ∃ u, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨u, -, hu, hV⟩ := (paddedVerifier_append C c V x v hv).mp h
    exact ⟨u, hu, hV⟩
  · rintro ⟨u, hu, hV⟩
    let k := (C + 1) * (x.length + 1) ^ c - (u.length + 1)
    have hroom : u.length + 1 ≤ (C + 1) * (x.length + 1) ^ c :=
      (Nat.add_le_add_right hu 1).trans (certificate_room C c x.length)
    have hv : (u ++ true :: List.replicate k false).length =
        (C + 1) * (x.length + 1) ^ c := by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      dsimp [k]
      omega
    refine ⟨_, hv, (paddedVerifier_append C c V x _ hv).mpr ?_⟩
    exact ⟨u, stripCertificate_pad u k, hu, hV⟩


/-- **Bounded-length paired certificates define the same class**
[AB09, Exercise 2.1, repaired per the phase-1 audit]: `L ∈ NP` iff there are
`C`, `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V`. The bounded form pairs
`x` with `u` via the audited self-delimiting `Turing.pairEncode`: with plain
concatenation the empty certificate would force `V ⊆ L` and collapse every
prefix-free language (audit finding 2, Argument B).

**Proof sketch.** (⇒) From the exact form `(C, c, V)`, take the paired verifier
`V' := {pairEncode x u : |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` with the same bound:
deciding `V'` parses the aligned pair (the `Turing.pairDecode` grammar; a
polynomial-time scan), checks the length equality against the explicit formula,
reassembles `x ++ u`, and runs `V`'s decider — each a named machine obligation
for the fill, none exotic. (⇐) From the bounded form `(C, c, V)`, take exact
length `R n = (C+1)(n+1)^c` — **admissible** for the repaired `NP`
(coefficient `C+1`, degree `c`; the round-2 audit refuted the earlier choice
`C(n+1)^c + 1`, which is not of the class's required shape — round-2
finding 1) — leaving `R n - C(n+1)^c = (n+1)^c ≥ 1` room for the marker. Pad
each certificate right-self-delimitingly to `u ++ [true] ++ false-run` of
length `R n`. The new verifier, on `y` of length `m`: search `n ≤ m` for
`n + R n = m` — strict increase of `n ↦ n + R n` gives **at most one**
solution, and none may exist (e.g. `y = []`, since `R n ≥ 1`): **reject if no
such `n` exists** (round-3 audit, finding 1); otherwise split `y = x ++ v` at
that unique `n` with
`|v| = R n ≥ 1`; reject if `v` has no `true` bit (so stripping never enters
`x`); split `v = u ++ [true] ++ false-run` at the **last** `true`; check the
*original* bound `|u| ≤ C(n+1)^c` — checkable precisely because the bound is
the explicit formula (phase-1 finding 2's residual error, fixed in round 1) —
and consult `V` on `pairEncode x u`. Every old witness pads within `R n`
(`|u| + 1 ≤ C(n+1)^c + 1 ≤ R n`); every accepted new witness strips back to
an old one (the round-2 audit's reconstruction, checked there across the
`C = 0`, `c = 0`, `x = []`, `u = []`, all-`false`, and malformed edge
cases). -/
theorem mem_NP_iff_exists_length_le {L : Language Bool} :
    L ∈ NP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V  := by
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, pairedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: aligned parsing, the explicit polynomial
      -- length-equality test, concatenation, and timed execution of V's decider.
      sorry
    · rw [hL x]
      constructor
      · rintro ⟨u, hu, hVu⟩
        exact ⟨u, hu.le, (pairedVerifier_pair C c V x u).mpr ⟨hu, hVu⟩⟩
      · rintro ⟨u, -, hVu⟩
        exact ⟨u, (pairedVerifier_pair C c V x u).mp hVu⟩
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C + 1, c, paddedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: bounded split search, last-true stripping,
      -- the original-bound test, pairing, and timed execution of V's decider.
      sorry
    · exact (hL x).trans (paddedVerifier_witness C c V x).symm

end Complexity


## ===== TCSlib/Complexity/ClassNP/EXP.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

open Turing Turing.FinTM

/-! ### Private certificate enumeration infrastructure -/

/-- Little-endian value, including leading zeroes at the high end. -/
private def enumValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * enumValue bs + if b then 1 else 0

/-- Increment without extending the width; `none` means exhaustion.
The empty word overflows, so its caller must test it before incrementing. -/
private def enumInc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (enumInc bs).map (false :: ·)

/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
private def enumWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)

/-- Every width-`w` word has value strictly below `2^w`. -/
private lemma enumValue_lt (u : List Bool) : enumValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [enumValue]
  | cons b u ih =>
    cases b <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.pow_succ] <;> omega

/-- The representation retains exactly the requested width, even at zero. -/
private lemma enumWord_length (w i : ℕ) : (enumWord w i).length = w := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih => simp only [enumWord, List.length_cons, ih]

/-- The initial rank is represented by precisely the all-false word. -/
private lemma enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- In range, the representation has the specified value.
**Proof sketch.** Remove the low bit by division by two. The quotient is
in range for the remaining width, and the remainder is either zero or one. -/
private lemma enumWord_value (w i : ℕ) (hi : i < 2 ^ w) :
    enumValue (enumWord w i) = i := by
  induction w generalizing i with
  | zero => simp only [Nat.pow_zero] at hi; simp [enumWord, enumValue, show i = 0 by omega]
  | succ w ih =>
    have hdiv : i / 2 < 2 ^ w := by rw [Nat.pow_succ] at hi; omega
    simp only [enumWord, enumValue, ih (i / 2) hdiv]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    split <;> simp_all <;> omega

/-- Equal-length words with the same value are equal, including trailing
false bits. The parity determines the first bit; divide the remainder by two. -/
private lemma enumValue_injective (u v : List Bool) (hlen : u.length = v.length)
    (hval : enumValue u = enumValue v) : u = v := by
  induction u generalizing v with
  | nil => simpa using hlen.symm
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons b' v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases b <;> cases b' <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte] at hval
      all_goals first | omega | exact congrArg (_ :: ·) (ih v hlen' (by omega))

/-- Every word is the unique representative of its rank at its own width. -/
private lemma enumWord_complete (u : List Bool) :
    enumWord u.length (enumValue u) = u := by
  exact enumValue_injective _ _ (enumWord_length _ _)
    (enumWord_value _ _ (enumValue_lt u))

/-- One fixed-width increment either preserves width and adds one to the
value, or reports overflow exactly at the last rank.
**Proof sketch.** A low false bit changes to true. A low true bit is cleared
and passes the carry to the suffix; suffix overflow is total overflow. -/
private lemma enumInc_spec (u : List Bool) :
    match enumInc u with
    | some v => v.length = u.length ∧ enumValue v = enumValue u + 1
    | none => enumValue u + 1 = 2 ^ u.length := by
  induction u with
  | nil => simp [enumInc, enumValue]
  | cons b u ih =>
    cases b with
    | false => simp [enumInc, enumValue]
    | true =>
      cases he : enumInc u with
      | none =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_none, enumValue, ↓reduceIte,
          List.length_cons, Nat.pow_succ]
        omega
      | some v =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_some, enumValue, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact ⟨by omega, by omega⟩

/-- On canonical candidates, increment advances exactly one rank and reports
overflow only after the last rank. This includes width zero. -/
private lemma enumInc_word (w i : ℕ) (hi : i < 2 ^ w) :
    enumInc (enumWord w i) =
      if i + 1 < 2 ^ w then some (enumWord w (i + 1)) else none := by
  have hs := enumInc_spec (enumWord w i)
  rw [enumWord_length, enumWord_value w i hi] at hs
  cases he : enumInc (enumWord w i) with
  | none => simp only [he] at hs; simp [show ¬i + 1 < 2 ^ w by omega]
  | some v =>
    simp only [he] at hs
    have hv := enumValue_lt v
    rw [hs.1, hs.2] at hv
    rw [if_pos hv]
    congr 1
    exact enumValue_injective v _ (hs.1.trans (enumWord_length _ _).symm)
      (hs.2.trans (enumWord_value w (i + 1) hv).symm)

/-- No candidate repeats among the `2^w` in-range ranks. -/
private lemma enumWord_no_repeat (w i j : ℕ) (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (h : enumWord w i = enumWord w j) : i = j := by
  have := congrArg enumValue h
  simpa only [enumWord_value w i hi, enumWord_value w j hj] using this

/-- Exact-width existential certificates are exactly the in-range candidates. -/
private lemma enumCandidates_iff (w : ℕ) (p : List Bool → Prop) :
    (∃ u, u.length = w ∧ p u) ↔ ∃ i, i < 2 ^ w ∧ p (enumWord w i) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact ⟨enumValue u, enumValue_lt u, by simpa only [enumWord_complete] using hu⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨enumWord w i, enumWord_length w i, hp⟩

/-- Resulting tape contents and success flag of a fixed-width carry. Overflow
clears the entire word and returns false; it never writes an extra bit. -/
private def enumBump : List Bool → List Bool × Bool
  | [] => ([], false)
  | false :: bs => (true :: bs, true)
  | true :: bs => (false :: (enumBump bs).1, (enumBump bs).2)

/-- The number of leading true bits crossed by the carry. -/
private def enumCarryPos : List Bool → ℕ
  | true :: bs => enumCarryPos bs + 1
  | _ => 0

/-- The carry visits at most the candidate width before detecting overflow. -/
private lemma enumCarryPos_le (u : List Bool) : enumCarryPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [enumCarryPos, List.length_cons] <;> omega

/-- The physical carry's tape contents always retain the original width. -/
private lemma enumBump_length (u : List Bool) : (enumBump u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [enumBump, ih]

/-- The carry's success flag and tape contents implement `enumInc` exactly. -/
private lemma enumBump_inc (u : List Bool) :
    enumInc u = if (enumBump u).2 then some (enumBump u).1 else none := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | false => rfl
    | true => simp only [enumInc, enumBump, ih]; split <;> rfl

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma enumBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma enumBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width increment, followed by a rewind. The live states are
carry (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def enumCarryTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some true => ⟨0, fun _ => (some (some false), .pos), none, some (.inl none)⟩
          | some false => ⟨0, fun _ => (some (some true), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the carry tape, with arbitrary native input-head position. -/
private def enumCarryCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg enumCarryTM.k Bool enumCarryTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One carry transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma enumCarry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    enumCarryTM.tm.step (enumCarryCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => enumCarryCfg x p (.inl (some false)) (pre.length - 1) pre
      | false :: us => enumCarryCfg x p (.inl (some true)) (pre.length - 1) (pre ++ true :: us)
      | true :: us => enumCarryCfg x p (.inl none) (pre.length + 1) (pre ++ false :: us) := by
  unfold MultiTapeTM.step
  change (enumCarryTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, enumBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact enumBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The carry phase takes one step beyond the leading true prefix, including
one blank test on overflow.
**Proof sketch.** Induct on the remaining candidate. Each true bit is cleared
and added to the processed prefix. A false bit or the right blank starts
rewind without changing the width. -/
private lemma enumCarry_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) pre.length (pre ++ u))
        (enumCarryPos u + 1) =
      enumCarryCfg x p (.inl (some (enumBump u).2))
        ((pre.length : ℤ) + enumCarryPos u - 1) (pre ++ (enumBump u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
      enumCarry_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | false =>
      simpa [enumCarryPos, enumBump, MultiTapeTM.runFrom_succ_eq_step] using
        enumCarry_step x p pre (false :: u)
    | true =>
      simp only [enumCarryPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCarry_step]
      simpa [enumBump, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [false])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma enumCarry_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = enumCarryCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : enumCarryTM.tm.step
        (enumCarryCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          enumCarryCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [enumCarryTM, enumCarryCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width increment and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading true-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns overflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma enumCarry_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * enumCarryPos u + 2 ≤ 2 * u.length + 2 ∧
      enumCarryTM.tm.runFrom (enumCarryCfg x p (.inl none) 0 u)
          (2 * enumCarryPos u + 2) =
        enumCarryCfg x p (.inr (enumBump u).2) 0 (enumBump u).1 := by
  refine ⟨by have := enumCarryPos_le u; omega, ?_⟩
  have hr := enumCarry_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * enumCarryPos u + 2 = (enumCarryPos u + 1) + (enumCarryPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact enumCarry_rewind x p (enumBump u).1 (enumBump u).2 _
    (by rw [enumBump_length]; exact enumCarryPos_le u)

section EnumCapture

variable {S : Type} [Fintype S] [DecidableEq S]
variable (M : FinTM Bool) (r : ℕ) (next : Option Bool → S)
variable (control : S → Option Bool → (Fin (M.k + (1 + r)) → Option Bool) →
  Action (M.k + (1 + r)) Bool (((Option M.State × Option Bool) × Bool) ⊕ S))

/-- Run a verifier on a work-tape input buffer, capture its first output bit
in finite control, and return live to a controller with access to all tapes.
The tape blocks are verifier work, input buffer, and `r` retained tapes.
The boundary tag supplies the verifier's native clamping behavior. The real
input head and retained tapes do not move during a call. -/
private def enumCaptureTM : FinTM Bool where
  k := M.k + (1 + r)
  State := ((Option M.State × Option Bool) × Bool) ⊕ S
  tm :=
    { q₀ := .inl ((some M.tm.q₀, none), true)
      tr := fun q inp work => match q with
        | .inl ((some q, reg), tag) =>
          let v := work (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1)))
          let a := M.tm.tr q v (fun i => work (Fin.castAdd (1 + r) i))
          let m := virtualMove tag v a.inputTape
          ⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
            some (.inl ((a.state, reg.or a.output), virtualNextTag tag m))⟩
        | .inl ((none, reg), _) => controlAction 0 (some (.inr (next reg)))
        | .inr q => control q inp work }

/-- A complete call invariant: exact source work tapes, an unchanged virtual
input buffer, arbitrary retained tapes, source output captured in finite
control, and empty physical output. The native input `x` can differ from
the verifier input `y`. -/
private def enumCaptureCfg {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) :
    Cfg (enumCaptureTM M r next control).k Bool
      (enumCaptureTM M r next control).State x where
  state := some (.inl ((cfg.state, cfg.output.head?), tag))
  inputPos := p
  workTapes := tapeBlocks cfg.workTapes (bufferTape y) tapes
  workTapePos := tapeBlocks cfg.workTapePos ((cfg.inputPos.val : ℤ) - 1) heads
  output := []

/-- One live source transition is simulated in one physical step, updating
the captured bit before recording a possible halt.
**Proof sketch.** Buffer reads equal native source reads. The virtual movement
lemma proves both clamping and preservation of the boundary tag. The verifier
work block changes in lockstep; the other tape contents are unchanged. The
head-of-append identity gives the captured bit, even on the halting action. -/
private lemma enumCapture_step {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hs : cfg.state ≠ none) :
    ∃ tag', VirtualTag (M.tm.step cfg).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.step
          (enumCaptureCfg M r next control cfg tag p tapes heads) =
        enumCaptureCfg M r next control (M.tm.step cfg) tag' p tapes heads := by
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    let m := virtualMove tag cfg.inputSymbol a.inputTape
    have hm := virtualMove_correct cfg tag htag a.inputTape
    have hc : M.tm.step cfg = a.apply cfg := by simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag tag m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs' : (enumCaptureCfg M r next control cfg tag p tapes heads).state =
          some (.inl ((some q, cfg.output.head?), tag)) := by simp [enumCaptureCfg, hq]
      have hv : (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.natAdd M.k (Fin.castAdd r (0 : Fin 1))) = cfg.inputSymbol := by
        simp [enumCaptureCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (enumCaptureCfg M r next control cfg tag p tapes heads).workTapeSymbols
          (Fin.castAdd (1 + r) i)) = cfg.workTapeSymbols := by
        funext i
        simp [enumCaptureCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs']
      dsimp only [enumCaptureTM]
      rw [hv, hr, hq]
      change (⟨0, tapeBlocks a.workTapes (none, m) (fun _ => (none, 0)), none,
        some (.inl ((a.state, cfg.output.head?.or a.output), virtualNextTag tag m))⟩ :
        Action (M.k + (1 + r)) Bool _).apply _ =
          enumCaptureCfg M r next control (a.apply cfg) _ p tapes heads
      refine Cfg.ext ?_ (moveInputPos_zero p) ?_ ?_ ?_
      · simp [enumCaptureCfg, Action.apply, List.head?_append, Option.head?_toList]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [enumCaptureCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [enumCaptureCfg, tapeBlocks, Action.apply]
      · simp [enumCaptureCfg, Action.apply]

/-- Lockstep through the first source halt, with an exact virtual-input
simulation, no physical emissions, and all retained tapes intact. -/
private lemma enumCapture_run {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (htag : VirtualTag cfg.inputPos tag) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    ∃ tag', VirtualTag (M.tm.runFrom cfg t).inputPos tag' ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control cfg tag p tapes heads) t =
        enumCaptureCfg M r next control (M.tm.runFrom cfg t) tag' p tapes heads := by
  induction t with
  | zero => exact ⟨tag, htag, rfl⟩
  | succ t ih =>
    obtain ⟨tag', htag', he⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨tag'', htag'', he'⟩ :=
      enumCapture_step M r next control _ tag' htag' p tapes heads (h t (by omega))
    refine ⟨tag'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using htag''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The administrative return step dispatches on the updated register and
preserves every tape, head, and the empty physical output. -/
private lemma enumCapture_transfer {x y : List Bool} (cfg : Cfg M.k Bool M.State y)
    (tag : Bool) (p : Fin (x.length + 2))
    (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ) (h : cfg.state = none) :
    (enumCaptureTM M r next control).tm.step
        (enumCaptureCfg M r next control cfg tag p tapes heads) =
      { enumCaptureCfg M r next control cfg tag p tapes heads with
        state := some (.inr (next cfg.output.head?)) } := by
  unfold MultiTapeTM.step
  simp only [enumCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Given a prepared buffer and fresh source tapes, a singleton-output call
returns its bit to the live controller within the source budget plus one.
This holds for any native input and parked head, including empty verifier
input. The complete returned configuration certifies retention and silence.
**Proof sketch.** Take the first source halting time. Start its virtual head
at cell zero with the right-boundary-compatible tag `true`. Apply lockstep
through the halt, then transfer. Absorbing source halting identifies its full
configuration with the one at the supplied budget. -/
private lemma enumCapture_returns (x y : List Bool) (b : Bool) (T : ℕ)
    (p : Fin (x.length + 2)) (tapes : Fin r → ℤ → Option Bool) (heads : Fin r → ℤ)
    (hM : M.ComputesInTime y [b] T) :
    ∃ t, t ≤ T + 1 ∧ ∃ tag,
      VirtualTag (M.tm.runFrom (M.tm.initCfg y) T).inputPos tag ∧
      (enumCaptureTM M r next control).tm.runFrom
          (enumCaptureCfg M r next control (M.tm.initCfg y) true p tapes heads) t =
        { enumCaptureCfg M r next control (M.tm.runFrom (M.tm.initCfg y) T)
            tag p tapes heads with state := some (.inr (next (some b))) } := by
  classical
  obtain ⟨hh, hout⟩ := (computesInTime_iff M y [b] T).mp hM
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg y) t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  have hs : (M.tm.runFrom (M.tm.initCfg y) t).state = none := Nat.find_spec hex
  have he : M.tm.runFrom (M.tm.initCfg y) T = M.tm.runFrom (M.tm.initCfg y) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  obtain ⟨tag, htag, hr⟩ := enumCapture_run M r next control (M.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    (fun s hs => Nat.find_min hex hs)
  refine ⟨t + 1, by omega, tag, by rwa [he], ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hr,
    enumCapture_transfer M r next control _ tag p tapes heads hs, ← he, hout]
  rfl

end EnumCapture

/-- Boolean result of testing `count` consecutive candidate ranks, starting
with `i`. The recursive branch represents one rejected call. -/
private def enumAny (accept : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => false
  | count + 1 => if accept i then true else enumAny accept (i + 1) count

/-- The abstract loop accepts exactly when an in-range candidate accepts.
**Proof sketch.** Separate the first rank from the remaining interval. -/
private lemma enumAny_iff (accept : ℕ → Bool) (i count : ℕ) :
    enumAny accept i count = true ↔
      ∃ j, i ≤ j ∧ j < i + count ∧ accept j = true := by
  induction count generalizing i with
  | zero =>
    simp only [enumAny, Bool.false_eq_true, false_iff]
    rintro ⟨j, hj, hj', _⟩
    omega
  | succ count ih =>
    change (if accept i then true else enumAny accept (i + 1) count) = true ↔ _
    by_cases h : accept i = true
    · simp only [if_pos h, true_iff]
      exact ⟨i, le_refl _, by omega, h⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hj', ha⟩
        exact ⟨j, by omega, by omega, ha⟩
      · rintro ⟨j, hj, hj', ha⟩
        have hne : j ≠ i := by intro he; subst j; exact h ha
        exact ⟨j, by omega, by omega, ha⟩

/-- For the actual verifier's indicator, testing all ranks gives exactly the
definition's existential over certificates of width `w`. This is independent
of the machine implementation, and includes width zero. -/
private lemma enumAny_certificates (x : List Bool) (w : ℕ) (V : Language Bool) :
    enumAny (fun i => MultiTapeTM.indicator V (x ++ enumWord w i)) 0 (2 ^ w) = true ↔
      ∃ u, u.length = w ∧ x ++ u ∈ V := by
  classical
  rw [enumAny_iff, enumCandidates_iff]
  simp [MultiTapeTM.indicator]

/-- A timed loop invariant combines bounded accept-or-advance segments into
one bounded singleton-output computation. The terminal configuration is the
post-overflow rejection configuration, so every candidate, including the last,
is tested before exhaustion.
**Proof sketch.** Induct on the remaining number of candidates. Acceptance
terminates immediately. Rejection advances to the next canonical configuration;
compose run segments and add their bounds. This lemma does not assert that
any particular machine satisfies the required per-round contracts. -/
private lemma enumLoop_run (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (accept : ℕ → Bool) (B i count : ℕ)
    (hend : (cfg (i + count)).state = none ∧ (cfg (i + count)).output = [false])
    (hround : ∀ j, i ≤ j → j < i + count → ∃ t, t ≤ B ∧
      if accept j then
        (M.tm.runFrom (cfg j) t).state = none ∧ (M.tm.runFrom (cfg j) t).output = [true]
      else M.tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t, t ≤ count * B ∧ (M.tm.runFrom (cfg i) t).state = none ∧
      (M.tm.runFrom (cfg i) t).output = [enumAny accept i count] := by
  induction count generalizing i with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [enumAny] using hend
  | succ count ih =>
    obtain ⟨t, ht, hc⟩ := hround i (le_refl _) (by omega)
    by_cases hb : accept i = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simpa [enumAny, hb] using hc.2
    · simp only [hb] at hc
      have hend' : (cfg (i + 1 + count)).state = none ∧
          (cfg (i + 1 + count)).output = [false] := by
        simpa only [show i + 1 + count = i + (count + 1) by omega] using hend
      obtain ⟨s, hs, hhalt, hout⟩ := ih (i + 1) hend'
        (fun j hj hj' => hround j (by omega) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [enumAny, hb] using hout

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma enumExponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- The audited round budget is pointwise bounded by an `EXP` budget, for
all coefficients and degrees, including zero.
**Proof sketch.** Set `k=max 1 c`. Both `n+1` and the width are bounded by
constant multiples of `(n+1)^k`. Replace the polynomial round overhead by
`2^(d·(n+width+1))`, add the exponents, and use `enumExponent_bound`. -/
private lemma enumBudget_bound (a C c d : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
        A * 2 ^ n ^ e := by
  let k := max 1 c
  let K := C + d * (C + 1)
  obtain ⟨A, e, hA⟩ := enumExponent_bound K k
  refine ⟨a * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 c)
  have hn : n + 1 ≤ (n + 1) ^ k := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left 1 c)
  have hw : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ k := by
    calc n + C * (n + 1) ^ c + 1 = (n + 1) + C * (n + 1) ^ c := by omega
         _ ≤ (n + 1) ^ k + C * (n + 1) ^ k :=
           Nat.add_le_add hn (Nat.mul_le_mul_left C hc)
         _ = (C + 1) * (n + 1) ^ k := by ring
  have he : C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
      K * (n + 1) ^ k := by
    calc C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
        C * (n + 1) ^ k + d * ((C + 1) * (n + 1) ^ k) :=
          Nat.add_le_add (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left d hw)
         _ = K * (n + 1) ^ k := by dsimp [K]; ring
  have hb : (n + C * (n + 1) ^ c + 1) ^ d ≤
      2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
    calc (n + C * (n + 1) ^ c + 1) ^ d ≤
        (2 ^ (n + C * (n + 1) ^ c + 1)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) d
         _ = 2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  calc a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
      a * (2 ^ (C * (n + 1) ^ c) * 2 ^ (d * (n + C * (n + 1) ^ c + 1))) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hb
       _ = a * 2 ^ (C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1)) := by
        rw [Nat.pow_add]
       _ ≤ a * 2 ^ (K * (n + 1) ^ k) :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) he)
       _ ≤ a * A * 2 ^ n ^ e := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (hA n)

/-- **Continuation frontier; admitted in this partial delivery.** There is one
uniform finite machine with a polynomial startup and a polynomially bounded
accept-or-advance segment for each exact-width candidate. The configuration
after the last rejected candidate is a halted singleton rejection.

**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
the all-false candidate while retaining the instance; assemble `x ++ u` on
the virtual input buffer. Use `enumCapture_returns` for the captured call.
On rejection, clear the bounded visited work region, reset all source and
buffer heads and the captured bit, and use `enumCarry_correct` to increment.
Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
overflow signal. Emit the single final answer only on acceptance or overflow.
Prove the startup and per-round configuration equalities below with a uniform
polynomial budget. These machine assembly and reset obligations are NOT
discharged by the counter, capture, and abstract loop lemmas alone. -/
private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  sorry

/-- Assuming the single machine-construction frontier, the proved loop
invariant gives a decider with the audited exponential-times-polynomial
budget. This lemma inherits exactly that pending admission.
**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
for all `2^width` candidates, and identify its Boolean answer using exact
candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
coefficient. The final computation has exactly one output bit. -/
private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
    ∃ (b e : ℕ) (E : FinTM Bool),
      E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
  classical
  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
  refine ⟨2 * b, e, E, fun x => ?_⟩
  obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
  let w := C * (x.length + 1) ^ c
  let B := b * (x.length + w + 1) ^ e
  let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
  obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
    (by simpa only [Nat.zero_add] using And.intro hend hout)
    (fun j _ hj => hround j (by simpa only [Nat.zero_add] using hj))
  have hb : enumAny accept 0 (2 ^ w) =
      MultiTapeTM.indicator
        {z | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x := by
    have ha := enumAny_certificates x w V
    change enumAny accept 0 (2 ^ w) = true ↔ _ at ha
    cases he : enumAny accept 0 (2 ^ w) with
    | false =>
      have hx : ¬∃ u, u.length = w ∧ x ++ u ∈ V := by
        intro hx
        have := ha.mpr hx
        rw [he] at this
        contradiction
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
    | true =>
      have hx := ha.mp he
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
  have hcomp : E.ComputesInTime x [enumAny accept 0 (2 ^ w)] (startup + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hinit]
    exact ⟨hh, ho⟩
  rw [hb] at hcomp
  apply hcomp.mono
  have hB : B ≤ 2 ^ w * B := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
       _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
       _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
machine — a **new obligation**; the explicit formula is what makes the width
computable at all, phase-1 audit finding 1 and question 4) and lay out a
width-`Q n` all-`false` candidate certificate; in each round, assemble
`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
candidate as a **fixed-width** counter and repeat, rejecting on width overflow
after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
definition's length — no majorant mismatch (audit question 4). The remaining
machine obligations, named for the fill per phase-1 finding 5 and round-2
finding 2: fixed-width increment with overflow detection (the private
`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
is a template, not a citable API — promotion or private re-derivation is a
fill-time decision); retention of `x` and the candidate across rounds;
**a verifier-call simulation that captures `MV`'s decision bit in finite
control, suppresses its physical emissions, and redirects its halt to the
loop controller** — the output tape is append-only, so forwarding per-round
emissions would accumulate (`[false, true]` across two rounds) and violate
`DecidesInTime`'s singleton contract; the real output stays empty until the
final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
and the captured bit between rounds (a bounded region — each head moves at
most one cell per step); and a timed loop invariant covering all of the above
(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
`L ∈ EXP`.
+
+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
+simulation, abstract timed-loop invariant, and final budget normalization
+are proved below the class definitions. The machine's initialization,
+reset, and controller assembly remain the single private admission
+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
  have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
    Set.ext (fun x => (hL x).symm)
  rw [heq] at hE
  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity


## ===== TCSlib/Complexity/TuringMachine.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.UniversalInterpreter
import TCSlib.Complexity.TuringMachine.UniversalBlock
import TCSlib.Complexity.TuringMachine.Universal

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Nondeterministic` — binary-choice nondeterministic machines [AB09, §2.1.2]:
  choice-word run semantics, all-branch halting, the bundled `FinNDTM` layer, and the
  deterministic embedding (the classes live in `ClassNP/NTIME`).
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `Sweep` — the generic zipper/transduction layer for sweep-based tape
  simulations, with the initialized-run head/support bound.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `Build/Convention`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives` — the
  machine-construction library (`machine-library-design.md`): the `Cfg.ofWords` seam
  discipline, the capture/silence and halt-redirect wrappers with the timed branch,
  the bounded-loop combinator, and the primitive catalog of timed string functions.
  Spec phase: contracts stated, fills pending, flagged for the shared infrastructure
  audit round.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
-/


## ===== scripts/ab_ch1_module_order.txt =====

TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Deterministic
TCSlib/Complexity/TuringMachine/StateRenaming
TCSlib/Complexity/TuringMachine/Finite
TCSlib/Complexity/TuringMachine/Oracle
TCSlib/Complexity/TuringMachine/Simulation
TCSlib/Complexity/TuringMachine/Sweep
TCSlib/Complexity/TuringMachine/Composition
TCSlib/Complexity/TuringMachine/Build/Convention
TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
TCSlib/Complexity/TuringMachine/Robustness/SingleTape
TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
TCSlib/Complexity/ClassP/DTIME
TCSlib/Complexity/ClassP/TimeConstructible
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/ClassP/P
TCSlib/Complexity/ClassP/ModelInvariance
TCSlib/Complexity/ClassP/Examples
TCSlib/Complexity/TuringMachine/Encoding
TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/Uncomputability/Computable
TCSlib/Complexity/Uncomputability/Diagonalization
TCSlib/Complexity/Uncomputability/Halting
TCSlib/Complexity/TuringMachine/Nondeterministic
TCSlib/Complexity/Formulas/CNF
TCSlib/Complexity/Formulas/CNFEncoding
TCSlib/Complexity/Formulas/DNF
TCSlib/Complexity/ClassNP/PolyTime
TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/CoNP
TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/Reductions
TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/TuringMachine
TCSlib/Complexity/ClassP
TCSlib/Complexity/Uncomputability
TCSlib/Complexity/Formulas
TCSlib/Complexity/CookLevin
TCSlib/Complexity/ClassNP


## ===== audits/ch2-epoch2-agent-reports/batchC.md =====

# Chapter 2, epoch 2, batch C — continuation checkpoint

**Status: incomplete, 2 of 3 targets filled. Do not close batch C on this archive.**

`HALT_NPHard` and `HALT_not_mem_NP` are filled and kernel-checked. Their only
admitted dependency is exactly the brief-sanctioned `Complexity.NP_subset_EXP`.
The full 53-module sweep passes with zero errors. All 34 new private helpers
are admission-free.

`mem_NP_iff_exists_length_le` remains admitted at two explicit machine
obligations: polynomial-time membership of the forward paired verifier and
the reverse padded verifier. The witness equivalences, search uniqueness,
padding/stripping specifications, and required rejection behavior are proved.
These semantic results do **not** discharge the machine obligations. Its
`sorryAx` is an outstanding defect under the completion criterion, not a
sanctioned dependency. This archive uses the brief's continuation provision;
`CONTINUATION.md` identifies the exact remaining work.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Base branch: `complexity/arora-barak-ch1`
- Base commit: `6c09453e6af59ff1575060b66196d28812800d24`
- Working branch, created off that exact base as the brief requires: `fill/ch2-e2-C`
- Delivered commit: `3a7201b13789c5c2f051e69203257f03d3d494c1`
- Delivered tree: `3382c0564df63e9b94e20b88f0534967b1bee538`
- Binding brief: `briefs/ch2-epoch2-batchC.md` at the base commit.
- Lean: `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent, no delegation.

Only the two owned tracked files changed:

- `TCSlib/Complexity/ClassNP/NP.lean`
- `TCSlib/Complexity/ClassNP/Reductions.lean`

No other branch was checked out or changed. There was no push or PR. All
existing public declarations, statement signatures, hypotheses, docstrings,
AB09 attributions, imports, and option headers are preserved. There are no
removed declarations or new public declarations. All existing non-target
declarations and their proofs are untouched.

## Target disposition, in the assigned order

| Target | Status | Work and remaining obligation |
|---|---|---|
| `mem_NP_iff_exists_length_le` | **Open** | Follows the audited two-verifier construction. Both witness equivalences are proved. Two inline `sorry` terms remain, each proving a verifier language is in `P`; neither is hidden in a helper. |
| `HALT_NPHard` | Filled | Uses `NP_subset_EXP`, normalizes the total singleton-indicator decider with `one_work_tape_binary`, transforms its control, applies `exists_codeTM`, and uses fixed-code prefixing. Only `decode_encode` is used of the representation scheme. |
| `HALT_not_mem_NP` | Filled | Converts the assumed NP membership through `NP_subset_EXP` to a total decider, proves its singleton indicator equals `[HALT c s]` on every string, and contradicts `HALT_not_computable`. The `EffectiveMachineCode` hypothesis is unchanged. |

The first target was developed before moving to the HALT pair. It is not
being reported as false or as unprovable: the missing work is construction
and timed verification of its two machines. No mathematical obstruction to
the frozen statement was found.

### Exercise 2.1: audited edge cases

These are semantic discharges; the pending timed machines must implement
the same checks.

| Edge case | Where discharged |
|---|---|
| `C = 0` | `certificate_room` is quantified over all natural coefficients. The old witness bound forces the empty witness, and `paddedVerifier_witness` pads it with a marker using coefficient `C+1`. No positivity hypothesis on `C` is used. |
| `c = 0` | `certificateTotal_strictMono` derives strictness from the additive input length, not strict growth of the power. `certificate_room` uses only `(n+1)^c ≥ 1`. Both proofs include degree zero. |
| `x = []` | `paddedVerifier_append` proves the recovered split for every input, including length zero; `take`/`drop` at that boundary recover the entire certificate region. |
| `u = []` | `stripCertificate_pad` includes an empty old witness. The marker itself is retained in the padded region, and `paddedVerifier_witness` proves its exact length. |
| All-false region | `stripCertificate_false` and `paddedVerifier_no_marker` prove rejection, including when the input contains true bits. Stripping operates only on the suffix after the recovered boundary. |
| Malformed strings | `pairedVerifier_malformed` rejects failed grammar parsing; `paddedVerifier_no_split` rejects missing length solutions. `certificateSplit_zero` covers empty total input. `stripCertificate_spec` characterizes every successful strip as a last-true decomposition. |
| Marker after too many witness bits | `paddedVerifier_too_long` proves rejection even for a correctly marked word of the enlarged exact width. The original bound is explicitly present in `paddedVerifier`. |

### HALT control modification

The named control-modification lemma is **`acceptTM_halts_iff`**; its run
invariant is `acceptTM_run`, derived from `acceptCfg_step`.

The state space is `Option (M.State × Bool)`. A simulated source state carries
the remembered bit; the inner `none` is a live loop state, distinct from a
configuration's outer `none` halting state. `acceptAction` first updates the
register with the action's optional output, then redirects the successor
state. Consequently an emission on the halting transition is included.
`acceptTM_loop` proves the stationary live configuration stays fixed at every
time. The real output is suppressed, and the tape count is unchanged.

The separate emit-then-copy machine is `prefixTM`. Its proved budget is
`|w| + |x| + 1`; `fixedPair_computes` explicitly specializes this to
`2|α| + |x| + 3`. It does not substitute the diagonal-pairing machine.

## New declarations

All names below are private, in namespace `Complexity`; there are **34**.
The axiom log checks every one, including definitions and theorems.

### NP.lean: 18 private declarations

| Name | Statement or role |
|---|---|
| `stripCertificate` | Removes the last true marker and its false suffix, returning failure if no marker exists. |
| `stripCertificate_false` | All-false input strips to failure. |
| `stripCertificate_pad` | A word followed by a marker and false run strips back to that word. |
| `stripCertificate_spec` | Failure is equivalent to being all false; success is equivalent to a last-true decomposition. |
| `certificateTotal_strictMono` | Input length plus repaired exact width is strictly increasing. |
| `certificate_room` | The repaired exact width exceeds the original bound by at least one. |
| `certificateSplit` | Executable bounded search for a legal length split. |
| `certificateSplit_spec` | The search returns a given index exactly when that index solves the length equation. |
| `certificateSplit_zero` | Total length zero has no legal split. |
| `pairedVerifier` | Forward verifier language, using `pairDecode`, the exact length test, and the old verifier. |
| `pairedVerifier_pair` | Membership on genuine pairs has exactly the intended meaning. |
| `pairedVerifier_malformed` | Failed pair parsing implies rejection. |
| `paddedVerifier` | Reverse verifier language, with split search, marker stripping, original-bound check, and old paired verification. |
| `paddedVerifier_no_split` | Failed split search implies rejection. |
| `paddedVerifier_append` | A correctly sized certificate region is split at exactly the original input boundary. |
| `paddedVerifier_no_marker` | An all-false certificate region is rejected. |
| `paddedVerifier_too_long` | An overlong stripped witness is rejected, even inside a valid exact-width region. |
| `paddedVerifier_witness` | Exact padded witnesses and old bounded paired witnesses are equivalent. |

### Reductions.lean: 16 private declarations

| Name | Statement or role |
|---|---|
| `acceptState` | Maps a source state and captured bit to a simulated, halting, or live-loop state. |
| `acceptAction` | Copies the source tape actions, updates the bit before halt redirection, and suppresses output. |
| `acceptTM` | Finite control-transformed machine with unchanged tape count. |
| `acceptCfg` | Configuration correspondence using the source output's last bit. |
| `acceptTM_loop` | Every run from the live loop configuration remains at that configuration. |
| `acceptCfg_apply` | Action application commutes with the configuration correspondence. |
| `acceptCfg_step` | The correspondence commutes with every source step. |
| `acceptTM_run` | Initialized runs correspond at every time. |
| `acceptTM_halts_iff` | For a total singleton-bit source decider, transformed halting is equivalent to a true bit. |
| `prefixTM` | Zero-work-tape fixed-prefix emission followed by input copying. |
| `prefixCfg` | Configuration notation for the prefix machine. |
| `prefixTM_emit` | Fixed-prefix phase run invariant. |
| `prefixTM_copy` | Input-copy phase run invariant. |
| `prefixTM_computes` | Exact linear bound for fixed prefixing, including the final halting step. |
| `fixedPair_computes` | Audited `2|α| + |x| + 3` bound for fixed-code pairing. |
| `fixedPair_polyTime` | Polynomial-time computability of fixed-code pairing. |

## Requested shared lemmas

For serial promotion at a maintainer's discretion:

1. An existential public fixed-prefixing theorem from `prefixTM_computes`,
   in the composition layer, with the same `|w| + |x| + 1` bound.
2. Its fixed-code pairing specialization from `fixedPair_computes`, in the
   encoding layer. This is distinct from diagonal pairing.

The implementations remain private in the owned file. No shared file was
modified. The two verifier constructions remain this batch's continuation
obligations, not assumed shared results.

## Escalations and continuation

**Completion escalation:** Exercise 2.1 is unfinished. Its direct `sorryAx`
root violates the brief's clean-target requirement, so the gate remains open.
There is no proposed statement alteration. Continue from the delivered
commit using `CONTINUATION.md`, replacing both verifier-membership admissions
with actual timed machine proofs. Preserve all frozen statements and the
audited route.

## Verification evidence

The dependency setup invoked `lake exe cache get`. The whole-Mathlib fetch
encountered repeated HTTP 502 responses and was stopped after the required
dependencies were available. Same-pin local caches supplied missing campaign
modules. The initial bootstrap's missing Mathlib module was repaired, then
the complete 53-module bootstrap retry passed. No dependency revision,
toolchain, or tracked build configuration was changed. No `lake build` was run.

Early scratch development used the same-pin previous-epoch olean tree;
subsequent owned-module checks and the final complete sweep used this
checkout's freshly emitted olean tree. The final gate invokes the committed
`scripts/lean_check_tree.sh` and requires each Lean process to exit zero,
emit no `error:` lines, and produce a fresh olean. It stops at any failure.

- Final sweep: **53/53 pass; zero `error:` lines**.
- Final admitted-declaration warnings: **30**: the one unfinished owned NP
  target, plus 29 out-of-scope declarations.
- `Reductions.lean`: no directly admitted declarations.
- New private helpers: **34/34 admission-free**.
- Owned-file style lint: **0 FAIL, 0 WARN**.
- Statement freeze: **13 existing public declarations unchanged**, both
  ordered signatures and multisets checked; no removals or public additions.
- `git diff --check`: passes.
- Patch replay on a separate index: reproduces the delivered tree exactly.
- Incremental bundle: verifies against the recorded base.

Final sweep tail:

```text
CHECK 51/53 TCSlib/Complexity/Formulas
RESULT 51/53 exit=0 seconds=1.318
CHECK 52/53 TCSlib/Complexity/CookLevin
RESULT 52/53 exit=0 seconds=1.567
CHECK 53/53 TCSlib/Complexity/ClassNP
RESULT 53/53 exit=0 seconds=1.478
PASS: 53/53 modules; seconds=184.992
UTC end: 2026-10-02T22:01:39.191581+00:00
```

### Axiom prints and verified roots

All three headlines currently print
`[propext, sorryAx, Classical.choice, Quot.sound]`. The set alone does not
distinguish a permitted dependency from an unfinished proof; kernel-environment
traversal does:

| Target | Declarations directly using `sorryAx` in its transitive dependency closure | Disposition |
|---|---|---|
| `mem_NP_iff_exists_length_le` | Only `Complexity.mem_NP_iff_exists_length_le` itself | **Unfinished, unsanctioned; continuation required.** |
| `HALT_NPHard` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |
| `HALT_not_mem_NP` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |

The traversal inspects checked kernel declarations, both types and values,
including opaque values. It checks every new helper has no direct admission
root and only a subset of `[propext, Classical.choice, Quot.sound]`. The
script deliberately reports the unfinished NP target as such; successful
execution of the diagnostic is **not** a claim that all targets meet the gate.

After recreating the fresh tree, run `verification/run_axioms.sh` with the
checkout path. The full raw results are in `logs/axioms.log`; the verifier
program is included. `verification/sweep.py` and `verification/check_freeze.py`
take the checkout path as their argument. Put the pinned Lean on `PATH`.

## Archive contents and integration

The archive includes this report, continuation instructions, the two full
modified sources, one `git format-patch` patch, an incremental git bundle,
the final sweep and axiom logs, supporting verification scripts/logs, the
committed module order, and `SHA256SUMS`. Every payload file except
`SHA256SUMS` itself is covered.

Verify with `sha256sum -c SHA256SUMS` in the unpacked root. The bundle requires
base `6c09453e6af59ff1575060b66196d28812800d24` and advertises only
`refs/heads/fill/ch2-e2-C`. The patch is suitable for the workflow's `git am -3`
integration, but **must not be mistaken for a completed batch**.

## Brief checklist

- [ ] Three targets filled — **only two are filled**.
- [x] Exercise 2.1 edge-case semantic discharges itemized.
- [x] HALT control-modification lemma named and proved.
- [x] Base hash and all new declarations listed.
- [x] Shared-lemma requests and completion escalation recorded.
- [x] Final full sweep and axiom logs supplied; sanctioned roots checked.
- [ ] Exercise 2.1 has no `sorryAx` — **still open**.
- [x] Diff restricted to owned files and named targets plus private helpers.
- [x] Full sources, patch, bundle, verification material, and checksums supplied.


## ===== backlog.md =====

# Backlog

The consolidated tracking file for the Arora-Barak campaign branch
(`complexity/arora-barak-ch1`) and adjacent repository work: human-review
design questions, queued and on-hold campaign work, deferred formalizations,
pending decisions, and housekeeping. Consolidated 2026-09-18 from the two
campaign plans, the audit resolutions records, and session assessments.

**Conventions.** This file is the *canonical home* of the human-review
question statements (§1) — the plans keep stable numbered stubs, since audit
documents cite the numbering — and the *tracking index* for everything else
(scope prose remains in the plans; decision-log history is never moved).
New items land here; an item leaves only by a decision recorded in the
relevant plan's decision log. From the next audit round onward this file
joins the bundle attachment set.

---

## 1. Human-review design questions (reserved — never closed by an automated gate)

Flagged for a **human** auditor/maintainer: the LLM audit rounds verify
correctness, but these are matters of architectural taste and trust-surface
policy.

### CH1-Q1 — the 3A Mathlib-computability bridge

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batch A);
`MathlibBridge.lean`, `Turing.exists_effectiveMachineCode`.*

The audited docstring sketch called for the canonizer machine to be
**hand-assembled from this repository's composition combinators** ("its
construction uses the composition combinators", optionally with a polynomial
`canonizerTime`). The delivered proof instead (i) proves the canonization
*function* primitive recursive, (ii) compiles it through **Mathlib's verified
recursion-theory pipeline** (`ToPartrec.Code.exists_code` →
`PartrecToTM2.tr_eval`), (iii) simulates the resulting TM2 stack machine in
our model with a bespoke private `bridgeTM`, and (iv) lands in the binary
alphabet via the proved `alphabet_reduction`, extracting the time bound by
finite maxima (no polynomial bound claimed — permitted, since
`canonizerTime` is existential). The batch flagged the deviation itself; the
maintainer verification pass confirmed the proof is sorry-free with the
standard axiom footprint and zero public-interface drift. **Open questions
for a human:** (a) is the heavyweight `Mathlib.Computability.TMToPartrec`
import into the TM tree acceptable, or should the bridge be quarantined
behind the planned phase-5 `MathlibBridge` module boundary (it effectively
front-runs that module)? (b) is the enlarged trust/review surface (Mathlib's
TM2 semantics + the private `bridgeTM` simulation, ~150 private
declarations) preferable to a longer but self-contained combinator
construction? (c) should the abandoned polynomial-`canonizerTime` claim be
recorded as permanently out of scope, or re-derived later from the
combinator route if one is ever written? Since the epoch-3→4 merge the
bridge lives in the dedicated `MathlibBridge.lean`, which implements the
quarantine that part (a) contemplates — the `TMToPartrec` import is confined
to that one module and nothing outside `exists_effectiveMachineCode` depends
on it — but the implemented quarantine does **not** dispose of this
question: parts (a)-(c) remain open for human review (epoch-4 audit,
finding 3: an earlier version of this text misplaced the bridge inside
`Encoding.lean`).

*Cross-link: part (c) gained relevance in Chapter 2 — see §3, "Polynomial
canonizer for a concrete scheme".*

### CH1-Q2 — the 3B universal-interpreter proof architecture

*Origin: `AroraBarakChapter1Plan.md` §5 (epoch 3, batches B + B2);
`Universal.lean`, `Turing.universal`.*

The proof followed the audited sketch's outline (prefix-only startup,
canonizer capture onto a table tape, four-work-tape interpreter with a fixed
finite controller), but the realized architecture is by far the campaign's
most involved artifact: 2465 lines (2831 after the epoch-4A timed fill), 104
private declarations built across two agent sessions (WIP `f191b918` +
continuation), a bespoke checkpoint relation (`universalRelation`) with
generic block-simulation assembly (`universal_block_run` /
`universal_from_blocks`), a virtual left boundary via a marker tape, a unary
state tape with group-wise table scanning, and an *exact* per-phase cost
ledger realized to `universalBlockBound = 3L + 5N + 20`. The kernel checks
all of it, and the public statement is frozen and audited — but the *design*
was never itself an audit deliverable at this level of detail. **Open
questions for a human:** (a) is this the right load-bearing shape — and
which parts (the capture wrapper, the block-run/`universal_run_join`
assembly, the marker-directed rewind and unary-copy gadget patterns, all
flagged by the agents as promotion candidates) should graduate to shared
modules rather than being re-derived? (b) is the exact-ledger posture
(`3L + 5N + 20` proved to the transition) worth its brittleness against any
future change to `CodeTM.serialize`, or should the maintained invariant be
an existential bound with the exact ledger demoted to documentation? (c)
does the interpreter's claim to *be* the book's universal machine (as
opposed to satisfying the frozen statement, which the kernel settles)
deserve a targeted human read of the construction's core definitions
(`UniversalControl`, `universalInterpreter`, `universalRelation`), given no
executable diagnostics of the whole interpreter ever ran (the batch-B smoke
tests aborted on deep recursion and were discarded)?

*Cross-link: question (b)'s exact ledger is now also load-bearing for the
Chapter-2 `TMSAT_mem_NP` fill (the quantitative public bridge, §2), which
will expose a form of the constant publicly.*

### CH2-Q1 — generality of `HALT_not_mem_NP`

*Origin: `AroraBarakChapter2Plan.md` (phase-1, round-2 audit, finding 3);
`ClassNP/Reductions.lean`.*

The statement is currently at `Turing.EffectiveMachineCode` generality
because its proof route reuses Chapter 1's `HALT_not_computable`, whose own
proof runs the universal evaluator. The round-2 auditor showed this
restriction is **not mathematically necessary**: a direct diagonalization —
the public diagonal-pairing machine, the searcher's finite-control transform
with the halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator —
proves `HALT` undecidable for *every* lawful `Turing.MachineCode` (and the
earlier "trivial-machine scheme" counterexample is unlawful: constant
decoding violates `decode_encode`). **The question:** add that diagonal
lemma as a new audited statement (a strengthening of Chapter 1's
uncomputability story that shares its main fill obligation, the
control-transform lemma, with `HALT_NPHard`) and generalize
`HALT_not_mem_NP` to `MachineCode` — or keep the conservative signature as a
documented API/proof-route restriction? Maintainer's provisional choice,
pending review: the conservative signature, with the docstring stating the
restriction honestly; the diagonal lemma is deliberately *not* slipped into
a repair round, since it would enlarge the audited surface of Chapter 1's
uncomputability chapter.

---

## 2. Campaign work queued or on hold

* **Chapter-2 fill campaign (E1-E5)** — **active** (hold lifted
  2026-10-02 after the ch-6 integration and audit closed). All four
  statement-phase gates closed; 59 audited-true admissions.
  **Epoch/batch partition recorded** in `AroraBarakChapter2Plan.md` §4
  (fill-campaign subsection): E1 assemblies + poly-calculus + formula
  mathematics (batches 1A–1D, 28 targets), E2 enumerator + compilations +
  Ex 2.1/HALT + `TMSAT` (2A–2D, 11), E3 padding + SAT track + snapshot
  locality (3A–3D, 14), E4 the Cook-Levin summit + TAUTOLOGY dual (4A–4B,
  6), E5 closure. Padding moved E2 → E3 (recorded refinement);
  `EXP_subset_NEXP` 1C → 3A (recorded amendment). **E1 integrated 2026-10-02**
  (27/27 targets filled, nine agent commits, freeze audit clean, 32
  admissions remain, zero `sorryAx` across all fills); **epoch-1 gate CLOSED**
  2026-10-02, single round, 0 blockers/majors
  (`audits/ch2-epoch1-resolutions.md`); 27/59 proved, 32 remain.
  Deferred from E1: promotion of 1D's `foldr_max_le_of_forall` **and its
  companion `le_foldr_max_of_mem`** (auditor suggestion) to a shared list
  utility (disposition D3).
  **E2 briefs issued** 2026-10-02
  (`briefs/ch2-epoch2-batch{A,B,C,D}.md`; 10 targets + the mandated
  `timed_universal` bridge statement; inheritances embedded verbatim;
  hardened repo/branch headers; D1 axiom wording).
  **E2 checkpoints integrated 2026-10-03 — all four batches partial, epoch
  gate OPEN** (four Codex commits `da8bd091`…`4b4cd418` off `6c09453e`;
  maintainer verification clean — deleted-lines, surface, replay, fresh
  53-module sweep with 29 direct admissions, axiom-root traversal matching
  every REPORT; logs `audits/logs/ch2-e2-checkpoint-{sweep,axioms}.log`;
  decision-log row in the ch2 plan). 5 of 10 target bodies written;
  admission-free closure: `timeConstructible_poly` only. Uniform frontier:
  concrete machine construction/timed integration (147 helpers delivered,
  145 admission-free). Open sites: 2A's single `enumMachine_contracts`
  (closes `NP_subset_EXP` **and** both HALT targets), 2B's
  `choiceVerifier ∈ P` + untouched reverse direction, 2C's two verifier
  memberships (`CONTINUATION.md` shipped), 2D's `D-MEM`/`D-WRAP`/`D-EMIT`
  (+ the bridge escalation — **RESOLVED 2026-10-03**: Chapter 1 exports
  `Turing.timed_universal_concrete` and the TMSAT bridge is discharged
  via `tmsat_concrete_coefficient` + monotonicity; `TMSAT_mem_NP` now
  roots at `D-MEM` alone, tree admissions 46; decision-log rows in both
  plans). 2C also requests promotion of `prefixTM`/`fixedPair`
  fixed-prefixing lemmas (held with D3; subsumed by Build P3/P6 at the
  shared round).
  Next (sequencing per the frozen library design, 2026-10-03; spec
  layer and bridge export both landed 2026-10-03): the shared
  infrastructure audit pack (Build spec surface + the bridge export and
  its TMSAT discharge) → gate → library fills (harvest-adaptation
  batches; loop flagged for continuation budget) → E2 continuation
  briefs citing the library → epoch-2 audit.
* **Machine-construction library** (`machine-library-design.md`, design
  FROZEN 2026-10-03; decision-log rows in `AroraBarakChapter1Plan.md`):
  `TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean` — 12
  primitives (P1–P12, harvest-heavy), capture/silence + halt-redirect +
  timed cond wrappers, the bounded-loop combinator factored from 2A's
  `enumMachine_contracts`. **Spec layer LANDED 2026-10-03** (design §9a
  refinements recorded): `Cfg.ofWords` seam + pure vocabulary fully
  proved; 18 sorried contracts (4 wrapper, 2 loop, 12 primitive); order
  list and facade at 57 modules. **Bridge export landed 2026-10-03**
  (`Turing.timed_universal_concrete`; TMSAT bridge discharged, tree
  admissions 46). **Infra audit pack prepared 2026-10-03**
  (`audits/ch1-infra-{pack,bundle}.md`; pre-pack repair of
  `exists_loopTM` disclosed — anchor-entry discipline + fuel-machine
  hypothesis; gate awaits `audits/ch1-infra-findings.md`) — next: the
  gate, then fills (harvest-adaptation batches; loop flagged for
  continuation budget). Subsumes 2C's
  `prefixTM`/`fixedPair` promotion requests. Dedup of superseded batch
  privates is an E5 closure task. Mathlib TM2 rejected as substrate
  (evaluation recorded in the ch1 decision log).
* **Audit-mandated fill-brief inheritances** (each brief must carry these
  verbatim from the cited records):
  - `NP_subset_EXP` enumerator: the contract-by-contract table —
    `audits/ch2-phase1-round3-findings.md` (via `…-resolutions.md`).
  - NTIME/Theorem-2.6 compilations: the simulator invariant tables and
    branch-correspondence contracts — `audits/ch2-phase2-findings.md`
    (note 3: no untimed composition or bare computability substitutions).
  - `TMSAT_mem_NP`: the `PolyBound` budget chain and the **new public
    quantitative bridge** for `timed_universal`'s constant — one simulator
    chosen before code and input, both success and timeout clauses, the
    suggested form `(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoiding a
    `PolyBound` import into Chapter 1; Chapter-1 surface growth via the
    shared-file mechanism, flagged for its own audit —
    `audits/ch2-phase3-{findings,reaudit-findings,resolutions}.md`.
  - `TMSAT_NPHard`: exact-value emission case table and the explicit `T'`
    deadline formula (never majorize the certificate length) — same records.
  - Cook-Levin emitter (E4): the six-stage output-silence contract **and**
    the round-2 boundary-check table, the product snapshot encoding, and the
    exact serialization-length ledger (never constant-per-clause) —
    `audits/ch2-phase4-{findings,reaudit-findings,resolutions}.md`.
  - Locality fills: strict `s < t` in `prevVisit`; keep no-write and
    write-blank distinct (`some none` erases); writes on the halting
    transition count — phase-4 Derivation A.
  - `TAUTOLOGY_mem_coNP`: the DNF evaluation-congruence bridge as a private
    lemma — phase-4 round 1, note 6.
* **Chapter-2 blueprint increment** — at campaign closure (E5), per the
  Chapter-1 precedent (dep-graph merge, writer agents, validator).

---

## 3. Deferred formalizations

### Chapter 1

* **Phase 5 (deliberately unscheduled; "a task for much later"):** the
  `O(T log T)` oblivious simulation ([AB09] §1.7 / Ex 1.6); the RAM-TM
  exercise (Ex 1.9); a fuller mathlib recursion-theory bridge beyond the
  `MathlibBridge` quarantine. *Origin: ch1 plan §5, decision of 2026-09-16.*
* **Waived model bridges** — revisit only if a downstream result ever needs
  a formal bridge: the append-only-output and start-marker-initialization
  conventions vs. [AB09]'s model (no read-write-output machine is
  formalized; no exact [AB09] step count is ever imported). *Origin: ch1
  plan §5 phase-2 notes; ch1 phase-2 audit findings 3/13.*
* **`Universal.lean` factoring** — 2831 lines (escalation recorded at
  epoch 4A): ~1100 lines are stopped-interpreter administrative copies
  forced by per-module `match` auxiliaries; the 4A report's three
  shared-lemma generalizations are the designated future factoring. Also
  CH1-Q2(a)'s promotion candidates. *Origin: ch1 decision log, epoch-4A row.*
* **Polynomial canonizer for a concrete scheme** (CH1-Q1(c) continued):
  Chapter 2's `TMSAT_mem_NP`/`TMSAT_NPComplete` now carry the hypothesis
  `PolyBound c.canonizerTime`; a combinator-built effective scheme with a
  *proved* polynomial canonizer would discharge the hypothesis for a
  concrete scheme and reconnect Q1(c). *Origin: ch2 phase-3 audit.*
* **Blueprint planner refinement** — writers flagged planner `\uses` edges
  not present in the cited proofs (reproduced verbatim per pipeline rules).
  *Origin: ch1 decision log, blueprint-extraction row.*

### Chapters 2-3

* **§2.4 web of reductions** (`INDSET`, `0/1 IPROG`, `dHAMPATH`, exercise
  problems) — each needs a graph/arithmetic encoding surface; the legacy
  `Complexity/NPReductions/*` files may eventually be **retargeted** as the
  structure-level halves (see §5). *Origin: ch2 plan §1.*
* **§2.5 decision-versus-search** (Theorem 2.18). *Origin: ch2 plan §1.*
* **Parsimonious and Levin reductions** ([AB09] §2.3.6). *Origin: ch2 plan §1.*
* **Ex 2.6, the universal NDTM** — Chapter 3's tool. *Origin: ch2 plan §1.*
* **Ex 2.30, Berman's theorem.** *Origin: ch2 plan §1.*
* **General Boolean formulas** — `TAUTOLOGY` is deliberately stated on the
  documented DNF fragment; a general-formula carrier (AST, evaluation,
  serialization) is new work, and any future general `TAUTOLOGY` must not be
  silently identified with the fragment. *Origin: ch2 phase-3/4 audits.*
* **`MathlibBridge` poly-time upgrade** (open lever): `bridgeTM` costs O(1)
  native steps per TM2 operation, so a Mathlib `TM2ComputableInPolyTime`
  certificate would transfer; would also serve the Chapter-6 bridges below.
  *Origin: ch2 plan decision log ("revisit at phase 3" — still open).*
* **Oracle complexity classes** (Chapter 3): `Oracle.lean` has the raw model
  and both lockstep embeddings, audited; the class layer, the
  persistent-vs-auto-erased query-tape statement (polynomial overhead only —
  constant overhead provably impossible), and relativization (Baker-Gill-
  Solovay) are future Chapter-3 work. *Origin: ch1 plan §5 phase-2 notes;
  session assessment 2026-09-18.*

### Chapter 6 bridge theorems (unblocked: surface audited, gate closed 2026-10-02)

The `complexity/arora-barak-ch6` branch (circuits, `P/poly` — proved,
sorry-free) and this branch are complementary; the missing ch-6 headliners
are exactly the machine-facing ones:

* **Theorem 6.6, `P ⊆ P/poly`** — their `SizeClasses.lean` defers it for
  want of "a machine model, the class `P`, and the oblivious-simulation
  theorem"; this branch supplies all three, and the phase-4 `Snapshot`
  locality layer is essentially the tableau-to-circuit core.
* **CKT-SAT `NP`-hardness** ([AB09] Thm 6.11's completeness half; their
  branch has Tseitin equisatisfiability + size bounds only).
* **Interface guidance inherited from the ch6-circuit audit**
  (`audits/ch6-circuits-findings.md`, notes 12–15): (i) build Thm 6.6's
  circuit family gate by gate against `OnlyUsesGates stdGateOps` —
  `Circuit.toFeedForward` is a semantic wrapper and supplies no general basis
  guarantee; (ii) reduce to tree CKT-SAT from the audited
  `Std.Sat.CNF ℕ` carrier (or via a finite-DAG Tseitin step), with a total
  string map sending malformed inputs to a fixed rejecting word such as
  `encodeSigma ⟨0, .node false []⟩`; (iii) renumber variables densely before
  unary indices (an identifier `2^k` costs `2^k` unary bits against a
  `k+1`-bit name); (iv) `P ⊊ P/poly` additionally needs the
  campaign-decidability → Mathlib `ComputablePred` bridge.
* **Karp-Lipton** (Thm 6.19) — needs the polynomial hierarchy, a new
  surface; **Meyer's theorem** — needs this branch's `EXP`.

---

## 4. Decisions pending (user)

* **Chapter-6 integration** — resolved in part: ch6 was merged into the
  campaign branch (`a2a2728b`), and the circuit nomenclature pass agreed
  with the ch6 authors landed 2026-10-01 in three commits: `HasLogDepth`
  → `HasPolylogDepth`; the `ACP` namespace unbundled (generic circuit
  material → `BoolCircuit`, the Razborov–Smolensky chain →
  `RazborovSmolensky`, `AC_GateOps` → `BoolCircuit.stdGateOps`);
  `FeedForwardCircuit.lean` relocated to
  `Complexity/CircuitComplexity/FeedForward.lean`, so `Complexity` no
  longer imports from `BooleanAnalysis` (verification:
  `scripts/circuit_module_order.txt`, the 23-module dependency sweep).
  Still open: their `Formulas.lean` defines `Literal`/`Term`/`DNF`/`CNF`
  at the **root namespace** (policy §1 leak; future ambiguity against
  `Std.Sat.CNF`/`Std.Sat.Literal`) — namespace choice deliberately
  deferred (user: `BoolCircuit` is not the right home for formulas);
  three CNF ecosystems coexist (their width-indexed `CNF n`, legacy
  `NPReductions.CNFFormula V`, the audited `Std.Sat.CNF ℕ`) with three
  SAT→3SAT artifacts; `UHalt.lean` introduces a **second computability
  framework** (Mathlib `ComputablePred` vs. the campaign's quarantine and
  its own `HALT_not_computable`); the merged circuit surface **passed the external audit protocol**
  2026-10-02 (three rounds, 0 blockers throughout;
  `audits/ch6-circuits-resolutions.md`, CLOSED) — campaign statements may
  cite its definitions, subject to the recorded divergences and the §3
  interface notes. The dangling `ch6/PLAN.md` references were repointed
  here in the round-1 repairs. Loose ends for the colleagues:
  `Basic.lean` at 674 lines (> 600 target); and the audit's sweep logs
  show the **LMN tree is not sorry-free** (five `sorry` warnings across
  `CircuitCompression`, `IterativeReduction`, `Depth3Switching`,
  `CircuitTreeManip`) — outside the audited surface, flagged for its
  authors.
* **Fill-campaign start** (§2) — on hold by the same instruction.
* **Disposition of the three §1 questions** — CH1-Q1, CH1-Q2, CH2-Q1.
* **`TCSlib.Tactics` blueprint exclusion** — 92 metaprogramming-scaffolding
  declarations deliberately excluded from the dataset; user may override.
  *Origin: ch1 blueprint-extraction row.*
* **Fate of `AroraBarakChapter1Plan.md` at merge** — graduate to `docs/` vs.
  superseded by the blueprint. *Origin: ch1 decision log (final row).*

---

## 5. Repository housekeeping

* **Legacy `Complexity/NPReductions/*`**: 14 pre-existing style-lint FAILs
  (missing docstrings/References), outside the campaign surface; eventual
  fate coupled to the §3 retargeting idea. The ch6 branch adds (clean,
  additive) counting lemmas to `SATTo3SAT.lean`.
* **Dependabot**: 88 alerts on the repository default branch (2 critical,
  16 high) — repo-level, unrelated to this branch's content.
* **`AGENTS.md` / `.claude/CLAUDE.md`** partially superseded by campaign
  practice (`workflow.md` §7 records the boundary): the `lean_proof/`-based
  flow and the LeanInfoView-only verification guidance predate the gate
  script; align or annotate eventually.
* **`audits/TEMPLATE.md`** predates the evolved pack format (attestation
  evidence separation, bundle conventions); refresh before the next fresh
  campaign starts from it.
* **`HANDOFF.md`** — the have→lemma extractor campaign's own tracking
  document; deliberately *not* absorbed here.


## ===== audits/evidence/ch1-infra/byte-attestation.txt =====

Corrected byte-level attestation (round-1 finding 6: the round-1 pack
labeled Unicode character counts as bytes). All figures below are UTF-8
byte counts and SHA-256 hashes of the exact delimited slices.
Old = e8dd3e57^ : TCSlib/Complexity/ClassNP/TMSAT.lean; New = current file.

relocated five-lemma block, old site: 4022 chars, 4085 bytes, sha256 13f1d70ebb2a5d1818c524dd6b05e06fed7f98675f948fd0c55eeb80f1267987
relocated five-lemma block, new site: 4022 chars, 4085 bytes, sha256 13f1d70ebb2a5d1818c524dd6b05e06fed7f98675f948fd0c55eeb80f1267987
block identity: IDENTICAL
  delimiters: from the serialization lemma's docstring opener to the
  start of the next docstring at the old site; same opener plus the
  old block's exact length at the new site.
bridge statement, old: 625 chars, 651 bytes, sha256 6284da9ec00cb364a445d3d4b0383f8774591ad0357c8511df0923f30bc4bd0a
bridge statement, new: 625 chars, 651 bytes, sha256 6284da9ec00cb364a445d3d4b0383f8774591ad0357c8511df0923f30bc4bd0a
statement identity: IDENTICAL
  delimiters: from 'theorem timed_universal_quantitative' up to, and
  excluding, ':= by'.


## ===== audits/evidence/ch1-infra/diff-universal-e8dd3e57.patch =====

diff --git a/TCSlib/Complexity/TuringMachine/Universal.lean b/TCSlib/Complexity/TuringMachine/Universal.lean
index facc8aec..f6bfefbf 100644
--- a/TCSlib/Complexity/TuringMachine/Universal.lean
+++ b/TCSlib/Complexity/TuringMachine/Universal.lean
@@ -2831,4 +2831,71 @@ theorem timed_universal (c : EffectiveMachineCode) :
       exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
     simpa only [timedAnswer, if_neg hh] using hu
 
+/-- **The concrete bounded-answer export** [AB09, §1.4.1, time-bounded universal
+simulation, with the realized constant]: the single simulator behind
+`Turing.timed_universal`, with its code-dependent quadratic coefficient written
+out in public vocabulary — the startup part
+`3|α| + canonizerTime(|α|) + |serialize| + 2·|bits(numStates)| + 2·q₀ + 16`
+plus the interpreter part `Turing.universalBlockBound` plus `14`. One simulator
+is chosen **before** the code, the input, and the deadline; both the success
+clause and the timeout clause of `Turing.timed_universal` are preserved
+verbatim.
+
+This is the maintainer export mandated by the Chapter-2 phase-3 audit and
+requested by the epoch-2 TMSAT delivery (bridge protocol, step 3): the Chapter-2
+bridge `timed_universal_quantitative` is discharged from this theorem by
+monotonicity, after its side's arithmetic bound on this displayed coefficient.
+No bound is asserted on the arbitrary existential witness of
+`Turing.timed_universal` — the witness exhibited here is the concrete machine of
+its proof, and the displayed coefficient is that proof's realized constant. No
+Chapter-2 notion appears. New public surface, flagged for the shared
+infrastructure audit round.
+
+**Proof sketch.** `timed_computes` states exactly this bound for the concrete
+simulator, with the startup written as `timedStartupBound`, whose definition is
+the displayed startup expression; the two clauses then follow from the
+deadline-inclusive answer `timedAnswer` by the same case analysis as
+`Turing.timed_universal` (success: the halted source's output is reported behind
+`true`; timeout: no completed output exists, so the source configuration is
+live and the answer is `[false]`). -/
+theorem timed_universal_concrete (c : EffectiveMachineCode) :
+    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
+      (∀ output : List Bool,
+        (c.decode α).toFinTM.ComputesInTime x output t →
+        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
+          (true :: output)
+          ((3 * α.length + c.canonizerTime α.length +
+              (c.decode α).serialize.length +
+              2 * (Nat.bits (c.decode α).numStates).length +
+              2 * (c.decode α).tm.q₀.val + 16 +
+              universalBlockBound c α + 14) * (t + 1) ^ 2)) ∧
+      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
+        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
+          [false]
+          ((3 * α.length + c.canonizerTime α.length +
+              (c.decode α).serialize.length +
+              2 * (Nat.bits (c.decode α).numStates).length +
+              2 * (c.decode α).tm.q₀.val + 16 +
+              universalBlockBound c α + 14) * (t + 1) ^ 2)) := by
+  refine ⟨timedUniversalTM c, fun α x t => ?_⟩
+  -- The displayed coefficient is definitionally `timedStartupBound` expanded.
+  have hu : (timedUniversalTM c).ComputesInTime
+      (pairEncode (pairEncode (Nat.bits t) α) x)
+      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
+      ((3 * α.length + c.canonizerTime α.length +
+          (c.decode α).serialize.length +
+          2 * (Nat.bits (c.decode α).numStates).length +
+          2 * (c.decode α).tm.q₀.val + 16 +
+          universalBlockBound c α + 14) * (t + 1) ^ 2) :=
+    timed_computes c α x t
+  constructor
+  · intro output hsource
+    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
+    simpa only [timedAnswer, hh, if_pos, ho] using hu
+  · intro hsource
+    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
+      intro hhalt
+      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
+    simpa only [timedAnswer, if_neg hh] using hu
+
 end Turing


## ===== audits/evidence/ch1-infra/diff-tmsat-e8dd3e57.patch =====

diff --git a/TCSlib/Complexity/ClassNP/TMSAT.lean b/TCSlib/Complexity/ClassNP/TMSAT.lean
index b513ff43..8492aea5 100644
--- a/TCSlib/Complexity/ClassNP/TMSAT.lean
+++ b/TCSlib/Complexity/ClassNP/TMSAT.lean
@@ -601,40 +601,6 @@ theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
 
 /-! ### Quantitative timed-universal bridge -/
 
-/-- A single timed simulator, selected before the code and input, preserves
-both successful completion and timeout with the explicit budget
-`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
-[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.
-
-**The phase-3-mandated bridge statement: new public surface for the epoch-2
-audit.** Its coefficient is the displayed function of the code length; no
-bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.
-
-**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
-timed simulator's construction, bound the decoded serialization length by the
-canonizer's output-time bound, and bound the state/header sizes by that
-serialization. The existing proof's coefficient is then at most the displayed
-coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
-`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
-`Universal.lean` are private. The public API exposes only the existential
-coefficient, so the construction cannot be reused through that API. This single
-bridge declaration is intentionally admitted under the brief's escalation
-protocol: the maintainer must export a quantitative concrete bounded-answer
-lemma from Chapter 1 (including its timeout branch) and discharge this proof.
-Chapter-1 sources are unchanged. -/
-theorem timed_universal_quantitative (c : EffectiveMachineCode) :
-    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
-      (∀ output : List Bool,
-        (c.decode α).toFinTM.ComputesInTime x output t →
-        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
-          (true :: output)
-          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
-      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
-        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
-          [false]
-          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
-  sorry
-
 /-- The canonizer's completed serialization cannot be longer than its run. -/
 private lemma tmsat_serialization_length (c : EffectiveMachineCode) (α : List Bool) :
     (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
@@ -709,6 +675,61 @@ private lemma tmsat_concrete_coefficient (c : EffectiveMachineCode) (α : List B
   unfold universalBlockBound
   omega
 
+/-- A single timed simulator, selected before the code and input, preserves
+both successful completion and timeout with the explicit budget
+`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
+[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.
+
+**The phase-3-mandated bridge statement: new public surface for the epoch-2
+audit.** Its coefficient is the displayed function of the code length; no
+bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.
+
+**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
+timed simulator's construction, bound the decoded serialization length by the
+canonizer's output-time bound, and bound the state/header sizes by that
+serialization. The existing proof's coefficient is then at most the displayed
+coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
+`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
+`Universal.lean` are private. The public API exposes only the existential
+coefficient, so the construction cannot be reused through that API. This single
+bridge declaration is intentionally admitted under the brief's escalation
+protocol: the maintainer must export a quantitative concrete bounded-answer
+lemma from Chapter 1 (including its timeout branch) and discharge this proof.
+Chapter-1 sources are unchanged.
+
+**Discharged (2026-10-03, maintainer serial merge).** Chapter 1 now exports
+`Turing.timed_universal_concrete`: the concrete simulator's bounded-answer
+theorem with the private startup expression expanded into public vocabulary
+and both clauses preserved. This proof is that export, the arithmetic bound
+`tmsat_concrete_coefficient` on its displayed coefficient, and
+`Turing.FinTM.ComputesInTime.mono`. The escalation paragraph above is
+retained as audit history; its final sentence described the pre-export
+state, and the export is flagged for the shared infrastructure audit
+round. -/
+theorem timed_universal_quantitative (c : EffectiveMachineCode) :
+    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
+      (∀ output : List Bool,
+        (c.decode α).toFinTM.ComputesInTime x output t →
+        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
+          (true :: output)
+          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
+      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
+        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
+          [false]
+          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
+  obtain ⟨U, hU⟩ := timed_universal_concrete c
+  refine ⟨U, fun α x t => ?_⟩
+  obtain ⟨hsucc, htimeout⟩ := hU α x t
+  have hle : (3 * α.length + c.canonizerTime α.length +
+      (c.decode α).serialize.length +
+      2 * (Nat.bits (c.decode α).numStates).length +
+      2 * (c.decode α).tm.q₀.val + 16 +
+      universalBlockBound c α + 14) * (t + 1) ^ 2 ≤
+      (3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2 :=
+    Nat.mul_le_mul_right _ (tmsat_concrete_coefficient c α)
+  exact ⟨fun output hout => (hsucc output hout).mono hle,
+    fun hnone => (htimeout hnone).mono hle⟩
+
 /-- The exact success-tagged output or timeout answer of a bounded source run. -/
 private def tmsatAnswer (c : MachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
   let cfg := (c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t


## ===== audits/evidence/ch1-infra/loop-as-of-a418f586.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L): a bounded loop with tape-resident
round state, specified at two granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template.
* `Turing.FinTM.exists_loopTM` is the **constructive combinator**: from a
  body machine whose startup and rounds are `Turing.Cfg.ofWords` seam
  contracts, there is one finite machine iterating the body under a fuel
  bound, with the exhaustion rejection and the total polynomial budget
  owned by the combinator. It is the generic form of the enumerator batch's
  admitted `enumMachine_contracts` — the statement that every fill batch
  died re-deriving concretely — turned into a once-and-for-all interface.

**Status: spec phase.** Both theorems and the seam helper are stated; the
proofs are the library fill's risk concentration (continuation budget
anticipated, frozen design §10). New Chapter-1 surface, flagged for the
shared infrastructure audit round.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2 — a body proves its own restore from its own invariant;
the generic clearing fallback via the visited-region bound of
`TCSlib.Complexity.TuringMachine.Sweep` is recorded in the design document).
A round either **accepts** — halts with the single verdict `[true]`,
nothing else ever emitted — or **advances** to the seam carrying the
stepped state word. The combinator caps the rounds at a fuel bound
computed from the input length only, rejecting with `[false]` on
exhaustion; acceptance within fuel is therefore the Boolean
`(List.range (R n + 1)).any …` of the abstract orbit, which is the shape
the Chapter-2 enumerator consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  sorry

end Turing

namespace Turing.FinTM

/-- **The loop combinator** (spec, fill pending — the generic form of the
enumerator batch's admitted `enumMachine_contracts`; the construction is
the library fill's risk concentration). Given a body machine with

* a **startup** contract: from its genuine initial configuration on `x` it
  reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying the
  initial state word `s0 x` on tape 0 (scratch blank), and
* a **round** contract: from the seam carrying any state word `s` it
  either halts with the verdict `[true]` within `T |x|` (when `acceptF s`)
  or reaches the seam carrying `stepF s` within `T |x|`,

there is one finite machine that, on every input `x`, emits the single
verdict bit of the first `R |x| + 1` orbit points
`s0 x, stepF (s0 x), …, stepF^[R |x|] (s0 x)` — `[false]` when none
accepts (fuel exhaustion) — within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`.

**Proof sketch.** The combinator machine embeds the body via the W1
capture discipline of `TCSlib.Complexity.TuringMachine.Build.Wrappers`
(the body's verdict is captured, never physically emitted until the end),
adds a fuel counter of `R |x|` in binary (`Turing.incFixed` is the counter
discipline; its startup uses the polynomial-evaluation primitive), runs
`Turing.loop_run` over the seam family, and emits the verdict or the
exhaustion rejection. The fuel arithmetic and phase overheads are absorbed
into `c`. -/
theorem exists_loopTM (body : FinTM Bool) (anchor : body.State)
    (stepF : List Bool → List Bool) (acceptF : List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x : List Bool) (s : List Bool),
      if acceptF s then
        ∃ t ≤ T x.length,
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
      else
        ∃ t ≤ T x.length,
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF (stepF^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

end Turing.FinTM


## ===== audits/evidence/ch1-infra/loop-as-of-d576814c.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the bounded loop

The control centerpiece of the machine-construction library
(`machine-library-design.md` §5, L): a bounded loop with tape-resident
round state, specified at two granularities.

* `Turing.loop_run` is the **summation lemma**: given a family of round
  configurations with an accept-or-advance contract, the run from round 0
  halts within the summed budget with the loop's single verdict bit. It is
  the generic form of the Chapter-2 enumerator's proved private
  `enumLoop_run`, whose proof is the harvest template.
* `Turing.FinTM.exists_loopTM` is the **constructive combinator**: from a
  body machine whose startup and rounds are `Turing.Cfg.ofWords` seam
  contracts, there is one finite machine iterating the body under a fuel
  bound, with the exhaustion rejection and the total polynomial budget
  owned by the combinator. It is the generic form of the enumerator batch's
  admitted `enumMachine_contracts` — the statement that every fill batch
  died re-deriving concretely — turned into a once-and-for-all interface.

**Status: spec phase.** Both theorems and the seam helper are stated; the
proofs are the library fill's risk concentration (continuation budget
anticipated, frozen design §10). New Chapter-1 surface, flagged for the
shared infrastructure audit round.

## The round discipline

Round state is one word on the body's tape 0; every other body tape is
scratch, blank at both seam ends of a round (body-restores-scratch, frozen
design decision 9.2 — a body proves its own restore from its own invariant;
the generic clearing fallback via the visited-region bound of
`TCSlib.Complexity.TuringMachine.Sweep` is recorded in the design document).
A round either **accepts** — halts with the single verdict `[true]`,
nothing else ever emitted — or **advances** to the seam carrying the
stepped state word. The combinator caps the rounds at a fuel bound
computed from the input length only, rejecting with `[false]` on
exhaustion; acceptance within fuel is therefore the Boolean
`(List.range (R n + 1)).any …` of the abstract orbit, which is the shape
the Chapter-2 enumerator consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the clocked-loop discipline is
  the folklore engine of the enumeration and diagonalization arguments,
  §2.1 / §3.1–3.2.)
-/

namespace Turing

/-- Round state on tape 0, scratch blank: the standard word assignment for
a loop body's seam configurations. -/
def stateWord (k : ℕ) (s : List Bool) : Fin k → List Bool :=
  fun i => if (i : ℕ) = 0 then s else []

/-- **The loop summation lemma** (spec, fill pending — the generic form of
the enumerator's proved `enumLoop_run`, which is the harvest template).
Given round configurations `cfg 0, …, cfg N` of one machine with empty
outputs, such that each round `j < N` within budget `B` either halts with
the verdict `[true]` (when `accept j`) or reaches `cfg (j+1)`, and the
exhaustion round `cfg N` halts with `[false]` within `B`: the run from
`cfg 0` halts within `(N + 1) · B` steps with the single verdict bit
`(List.range N).any accept`.

**Proof sketch.** Induction on the first accepting round (or `N` when none
accepts), composing the advance segments with
`Turing.MultiTapeTM.runFrom_add` and absorbing halted tails with
`Turing.MultiTapeTM.runFrom_of_halt`; empty round outputs make the final
output exactly the one emitted verdict. -/
theorem loop_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hout : ∀ j ≤ N, (cfg j).output = [])
    (hend : ∃ t ≤ B, (tm.runFrom (cfg N) t).state = none ∧
      (tm.runFrom (cfg N) t).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ (N + 1) * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  sorry

end Turing

namespace Turing.FinTM

/-- **The loop combinator** (spec, fill pending — the generic form of the
enumerator batch's admitted `enumMachine_contracts`; the construction is
the library fill's risk concentration). Given a fuel machine and a body
machine with

* a **fuel** contract: `F` writes the round bound `R |x|` in binary within
  `T |x|` (an arbitrary `R : ℕ → ℕ` is not machine-evaluable, so the
  combinator must be handed its fuel; the enumerator's `2^w` and the
  split search's `n + 1` both have immediately writable bit patterns),
* a **startup** contract: from its genuine initial configuration on `x`
  the body reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying
  the initial state word `s0 x` on tape 0 (scratch blank), **without
  visiting the anchor state earlier**, and
* a **round** contract: from the seam carrying any state word `s` it
  either halts with the verdict `[true]` within `T |x|` (when `acceptF s`)
  or reaches the seam carrying `stepF s` within `T |x|` — in both cases
  **without re-entering the anchor state strictly between the seam and
  that endpoint**,

there is one finite machine that, on every input `x`, emits the single
verdict bit of the first `R |x| + 1` orbit points
`s0 x, stepF (s0 x), …, stepF^[R |x|] (s0 x)` — `[false]` when none
accepts (fuel exhaustion) — within a constant multiple of
`(T |x| + 1) · (R |x| + 2)`.

The two discipline clauses are load-bearing (maintainer pre-audit
adversarial pass, recorded for the shared infrastructure round): the
combinator's host detects round boundaries **as entries into the embedded
anchor state**, so a mid-round anchor visit would decrement the fuel
early and change the computed function; and without the fuel machine the
statement would assert a finite machine materializing an arbitrary
natural-number function of the input length.

**Proof sketch.** The combinator machine runs `F` relocated-and-captured
to lay the fuel word on a counter tape, rewinds, and embeds the body via
the W1 capture discipline of
`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
captured, never physically emitted until the end). On each entry into the
embedded anchor it decrements the binary counter in place; the borrow
discipline is amortized — total countdown cost over all rounds is linear
in `R |x|` plus the counter width, and exhaustion is detected exactly
when a borrow runs off the counter's end, which is what keeps the stated
budget at `(T + 1) · (R + 2)` rather than acquiring a logarithmic factor.
`Turing.loop_run` sums the seam family; acceptance surfaces as the
captured halt (`[true]`), and borrow-overflow emits the exhaustion
rejection (`[false]`). Phase overheads are absorbed into `c`. -/
theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
    (stepF : List Bool → List Bool) (acceptF : List Bool → Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x : List Bool) (s : List Bool),
      ∃ t ≤ T x.length,
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF (stepF^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) := by
  sorry

end Turing.FinTM


## ===== audits/evidence/ch1-infra/import-grep.txt =====

TCSlib/Complexity/TuringMachine.lean:15:import TCSlib.Complexity.TuringMachine.Build.Convention
TCSlib/Complexity/TuringMachine.lean:16:import TCSlib.Complexity.TuringMachine.Build.Wrappers
TCSlib/Complexity/TuringMachine.lean:17:import TCSlib.Complexity.TuringMachine.Build.Loop
TCSlib/Complexity/TuringMachine.lean:18:import TCSlib.Complexity.TuringMachine.Build.Primitives
TCSlib/Complexity/TuringMachine/Build/Convention.lean:19:`TCSlib.Complexity.TuringMachine.Build.Primitives` are stated against.
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:6:import TCSlib.Complexity.TuringMachine.Build.Convention
TCSlib/Complexity/TuringMachine/Build/Loop.lean:7:import TCSlib.Complexity.TuringMachine.Build.Convention
TCSlib/Complexity/TuringMachine/Build/Loop.lean:150:`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7:import TCSlib.Complexity.TuringMachine.Build.Convention


## ===== audits/evidence/ch1-infra/diff-lean-runB-runC.txt =====

Lean-source changes between e8dd3e57 (run B) and d576814c (run C):
 TCSlib/Complexity/TuringMachine/Build/Loop.lean | 66 ++++++++++++++++++-------
 1 file changed, 47 insertions(+), 19 deletions(-)

Full diff:
diff --git a/TCSlib/Complexity/TuringMachine/Build/Loop.lean b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
index 259f4309..ea6deada 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Loop.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
@@ -3,6 +3,7 @@ Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Seyoon Ragavan
 -/
+import Mathlib.Data.Nat.Bits
 import TCSlib.Complexity.TuringMachine.Build.Convention
 import TCSlib.Complexity.TuringMachine.Composition
 
@@ -100,14 +101,22 @@ namespace Turing.FinTM
 
 /-- **The loop combinator** (spec, fill pending — the generic form of the
 enumerator batch's admitted `enumMachine_contracts`; the construction is
-the library fill's risk concentration). Given a body machine with
-
-* a **startup** contract: from its genuine initial configuration on `x` it
-  reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying the
-  initial state word `s0 x` on tape 0 (scratch blank), and
+the library fill's risk concentration). Given a fuel machine and a body
+machine with
+
+* a **fuel** contract: `F` writes the round bound `R |x|` in binary within
+  `T |x|` (an arbitrary `R : ℕ → ℕ` is not machine-evaluable, so the
+  combinator must be handed its fuel; the enumerator's `2^w` and the
+  split search's `n + 1` both have immediately writable bit patterns),
+* a **startup** contract: from its genuine initial configuration on `x`
+  the body reaches, within `T |x|`, the seam `Turing.Cfg.ofWords` carrying
+  the initial state word `s0 x` on tape 0 (scratch blank), **without
+  visiting the anchor state earlier**, and
 * a **round** contract: from the seam carrying any state word `s` it
   either halts with the verdict `[true]` within `T |x|` (when `acceptF s`)
-  or reaches the seam carrying `stepF s` within `T |x|`,
+  or reaches the seam carrying `stepF s` within `T |x|` — in both cases
+  **without re-entering the anchor state strictly between the seam and
+  that endpoint**,
 
 there is one finite machine that, on every input `x`, emits the single
 verdict bit of the first `R |x| + 1` orbit points
@@ -115,31 +124,50 @@ verdict bit of the first `R |x| + 1` orbit points
 accepts (fuel exhaustion) — within a constant multiple of
 `(T |x| + 1) · (R |x| + 2)`.
 
-**Proof sketch.** The combinator machine embeds the body via the W1
-capture discipline of `TCSlib.Complexity.TuringMachine.Build.Wrappers`
-(the body's verdict is captured, never physically emitted until the end),
-adds a fuel counter of `R |x|` in binary (`Turing.incFixed` is the counter
-discipline; its startup uses the polynomial-evaluation primitive), runs
-`Turing.loop_run` over the seam family, and emits the verdict or the
-exhaustion rejection. The fuel arithmetic and phase overheads are absorbed
-into `c`. -/
-theorem exists_loopTM (body : FinTM Bool) (anchor : body.State)
+The two discipline clauses are load-bearing (maintainer pre-audit
+adversarial pass, recorded for the shared infrastructure round): the
+combinator's host detects round boundaries **as entries into the embedded
+anchor state**, so a mid-round anchor visit would decrement the fuel
+early and change the computed function; and without the fuel machine the
+statement would assert a finite machine materializing an arbitrary
+natural-number function of the input length.
+
+**Proof sketch.** The combinator machine runs `F` relocated-and-captured
+to lay the fuel word on a counter tape, rewinds, and embeds the body via
+the W1 capture discipline of
+`TCSlib.Complexity.TuringMachine.Build.Wrappers` (the body's verdict is
+captured, never physically emitted until the end). On each entry into the
+embedded anchor it decrements the binary counter in place; the borrow
+discipline is amortized — total countdown cost over all rounds is linear
+in `R |x|` plus the counter width, and exhaustion is detected exactly
+when a borrow runs off the counter's end, which is what keeps the stated
+budget at `(T + 1) · (R + 2)` rather than acquiring a logarithmic factor.
+`Turing.loop_run` sums the seam family; acceptance surfaces as the
+captured halt (`[true]`), and borrow-overflow emits the exhaustion
+rejection (`[false]`). Phase overheads are absorbed into `c`. -/
+theorem exists_loopTM (body F : FinTM Bool) (anchor : body.State)
     (stepF : List Bool → List Bool) (acceptF : List Bool → Bool)
     (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
+    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
     (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
+      (∀ t' < t,
+        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
       body.tm.runFrom (body.tm.initCfg x) t =
         Cfg.ofWords anchor (stateWord body.k (s0 x)))
     (hround : ∀ (x : List Bool) (s : List Bool),
-      if acceptF s then
-        ∃ t ≤ T x.length,
+      ∃ t ≤ T x.length,
+        (∀ t', 0 < t' → t' < t →
+          (body.tm.runFrom
+            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
+              ≠ some anchor) ∧
+        if acceptF s then
           (body.tm.runFrom
             (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
               = none ∧
           (body.tm.runFrom
             (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
               = [true]
-      else
-        ∃ t ≤ T x.length,
+        else
           body.tm.runFrom
             (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
               Cfg.ofWords anchor (stateWord body.k (stepF s))) :


## ===== audits/programs/ch1-infra-BuildSpecAxioms.lean =====

import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0

-- Machine-library spec layer, maintainer attestation (round 2: 22 contracts).
-- (1) The Chapter-1 headline regression set must stay admission-free: the Build
-- modules are only imported, outside the Build subgraph, by the facade, so their
-- sorried contracts must not reach any headline print.
#print axioms Turing.timed_universal
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Turing.exists_effectiveMachineCode
#print axioms Complexity.HALT_not_computable

-- (2) The Convention module is fully proved: its glue must be admission-free.
#print axioms Turing.initCfg_ofWords
#print axioms Turing.Cfg.ofWords_workTapes

-- (3) The 22 sorried spec contracts, printed to pin the expected admission set
-- of this commit (each must show sorryAx; nothing else in the tree gains one).
#print axioms Turing.capture_run
#print axioms Turing.FinTM.redirectTM_computes
#print axioms Turing.FinTM.redirectTM_live
#print axioms Turing.FinTM.computesFunInTime_cond
#print axioms Turing.loop_run
#print axioms Turing.FinTM.exists_loopTM
#print axioms Turing.FinTM.exists_loopFindTM
#print axioms Turing.FinTM.computesFunInTime_prepend
#print axioms Turing.FinTM.computesFunInTime_lengthBits
#print axioms Turing.FinTM.computesFunInTime_polyUnary
#print axioms Turing.FinTM.computesFunInTime_polyBits
#print axioms Turing.FinTM.computesFunInTime_pairEncodeFixed
#print axioms Turing.FinTM.computesFunInTime_pairFst
#print axioms Turing.FinTM.computesFunInTime_pairSnd
#print axioms Turing.FinTM.computesFunInTime_pairValid
#print axioms Turing.FinTM.computesFunInTime_pairConcat
#print axioms Turing.FinTM.computesFunInTime_pairDup
#print axioms Turing.FinTM.computesFunInTime_pairMapSnd
#print axioms Turing.FinTM.computesFunInTime_pairLenCheck
#print axioms Turing.FinTM.computesFunInTime_stripLast
#print axioms Turing.FinTM.computesFunInTime_splitSolve
#print axioms Turing.FinTM.computesFunInTime_incFixed


## ===== audits/programs/ch1-infra-BridgeExportAxioms.lean =====

import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassNP
import Lean

set_option maxHeartbeats 0

-- Maintainer axiom attestation: Chapter-1 bridge export + TMSAT bridge discharge.
-- (1) The export and the discharged bridge must be admission-free.
#print axioms Turing.timed_universal_concrete
#print axioms Complexity.timed_universal_quantitative
-- (2) The Chapter-1 headline regression set stays admission-free.
#print axioms Turing.timed_universal
#print axioms Turing.universal
#print axioms Turing.universal_quadratic
#print axioms Turing.exists_effectiveMachineCode
#print axioms Complexity.HALT_not_computable
-- (3) The TMSAT targets' remaining roots shrink exactly as expected.
#print axioms Complexity.TMSAT_mem_NP
#print axioms Complexity.TMSAT_NPHard
#print axioms Complexity.TMSAT_NPComplete

open Lean Elab Command

namespace BridgeAudit

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

/-- Traverse checked kernel declarations, including opaque values and types. -/
partial def visit (name : Name) : WalkM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      modify fun s => { s with roots := s.roots.push name }
    deps.forM visit
    match ci with
    | .inductInfo i => i.ctors.forM visit
    | _ => pure ()

def roots (env : Environment) (name : Name) : Array Name :=
  (((visit name).run env).run {}).2.roots

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def userRoots (env : Environment) (name : Name) : List Name :=
  ((roots env name).map privateToUserName).toList.eraseDups.mergeSort
    (fun a b => a.toString ≤ b.toString)

run_cmd do
  let env ← getEnv
  let expectations : Array (Name × List Name) := #[
    (``Turing.timed_universal_concrete, []),
    (``Complexity.timed_universal_quantitative, []),
    (``Turing.timed_universal, []),
    (``Complexity.TMSAT_mem_NP, [``Complexity.TMSAT_mem_NP]),
    (``Complexity.TMSAT_NPHard, [``Complexity.TMSAT_NPHard]),
    (``Complexity.TMSAT_NPComplete,
      [``Complexity.TMSAT_mem_NP, ``Complexity.TMSAT_NPHard]),
    -- Regression: the epoch-2 A/C cluster is untouched by this change.
    (``Complexity.NP_subset_EXP, [`Complexity.enumMachine_contracts]),
    (``Complexity.HALT_NPHard, [`Complexity.enumMachine_contracts])]
  for (name, expectedRaw) in expectations do
    let expected := expectedRaw.eraseDups.mergeSort (fun a b => a.toString ≤ b.toString)
    let found := userRoots env name
    logInfo m!"ROOTS {name}: {found}"
    unless found == expected do
      throwError "Unexpected admission roots for {name}: {found}; expected {expected}"
    let ax ← collectAxioms name
    unless ax.all (fun a => allowed.contains a || a == ``sorryAx) do
      throwError "Unexpected axiom for {name}: {ax}"
    if expected.isEmpty && ax.contains ``sorryAx then
      throwError "Unexpected sorryAx for {name}"
    unless expected.isEmpty || ax.contains ``sorryAx do
      throwError "Expected sorryAx for {name} but it is absent"
  logInfo "BRIDGE AUDIT PASS: the export and the discharged bridge are admission-free; TMSAT roots shrank exactly to their D-sites; headline and epoch-2 regressions unchanged."

end BridgeAudit


## ===== audits/logs/ch1-build-spec-sweep.log =====

machine-library spec layer: full fresh sweep (57 modules)
START_UTC: 2026-10-03T06:59:47Z
=== 1/57 TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 2/57 TCSlib/Complexity/TuringMachine/Deterministic
=== 3/57 TCSlib/Complexity/TuringMachine/StateRenaming
=== 4/57 TCSlib/Complexity/TuringMachine/Finite
=== 5/57 TCSlib/Complexity/TuringMachine/Oracle
=== 6/57 TCSlib/Complexity/TuringMachine/Simulation
=== 7/57 TCSlib/Complexity/TuringMachine/Sweep
=== 8/57 TCSlib/Complexity/TuringMachine/Composition
=== 9/57 TCSlib/Complexity/TuringMachine/Build/Convention
=== 10/57 TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:135:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:190:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:206:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:226:8: warning: declaration uses 'sorry'
=== 11/57 TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Loop.lean:126:8: warning: declaration uses 'sorry'
=== 12/57 TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
=== 13/57 TCSlib/Complexity/TuringMachine/Robustness/SingleTape
=== 14/57 TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
=== 15/57 TCSlib/Complexity/ClassP/DTIME
=== 16/57 TCSlib/Complexity/ClassP/TimeConstructible
=== 17/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
=== 18/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 19/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 20/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
=== 21/57 TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 22/57 TCSlib/Complexity/ClassP/P
=== 23/57 TCSlib/Complexity/ClassP/ModelInvariance
=== 24/57 TCSlib/Complexity/ClassP/Examples
=== 25/57 TCSlib/Complexity/TuringMachine/Encoding
=== 26/57 TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:66:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:79:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:96:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:113:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:131:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:145:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:173:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:237:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:258:8: warning: declaration uses 'sorry'
=== 27/57 TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 28/57 TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:448:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:454:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:459:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:484:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:490:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:495:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:719:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:821:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 29/57 TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 30/57 TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 31/57 TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 32/57 TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:314:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:337:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:362:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:427:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:434:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:470:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:477:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:487:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:621:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:644:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:659:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:638:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:684:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:761:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:820:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:847:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:889:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:897:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1006:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1106:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1578:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1606:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2278:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 33/57 TCSlib/Complexity/Uncomputability/Computable
=== 34/57 TCSlib/Complexity/Uncomputability/Diagonalization
=== 35/57 TCSlib/Complexity/Uncomputability/Halting
=== 36/57 TCSlib/Complexity/TuringMachine/Nondeterministic
=== 37/57 TCSlib/Complexity/Formulas/CNF
=== 38/57 TCSlib/Complexity/Formulas/CNFEncoding
=== 39/57 TCSlib/Complexity/Formulas/DNF
=== 40/57 TCSlib/Complexity/ClassNP/PolyTime
=== 41/57 TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/NP.lean:359:8: warning: declaration uses 'sorry'
=== 42/57 TCSlib/Complexity/ClassNP/CoNP
=== 43/57 TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:750:16: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/EXP.lean:879:8: warning: declaration uses 'sorry'
=== 44/57 TCSlib/Complexity/ClassNP/Reductions
=== 45/57 TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
=== 46/57 TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:672:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:712:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:722:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:742:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:763:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:774:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:810:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:816:8: warning: declaration uses 'sorry'
=== 47/57 TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:120:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:155:8: warning: declaration uses 'sorry'
=== 48/57 TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/ClassNP/TMSAT.lean:625:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/TMSAT.lean:930:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/TMSAT.lean:1119:8: warning: declaration uses 'sorry'
=== 49/57 TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Snapshot.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:192:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:204:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:244:8: warning: declaration uses 'sorry'
=== 50/57 TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
=== 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
=== 52/57 TCSlib/Complexity/TuringMachine
=== 53/57 TCSlib/Complexity/ClassP
=== 54/57 TCSlib/Complexity/Uncomputability
=== 55/57 TCSlib/Complexity/Formulas
=== 56/57 TCSlib/Complexity/CookLevin
=== 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
END_UTC: 2026-10-03T07:01:18Z


## ===== audits/logs/ch1-bridge-export-sweep.log =====

ch1 bridge export + TMSAT bridge discharge: full fresh sweep (57 modules)
START_UTC: 2026-10-03T07:11:10Z
=== 1/57 TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 2/57 TCSlib/Complexity/TuringMachine/Deterministic
=== 3/57 TCSlib/Complexity/TuringMachine/StateRenaming
=== 4/57 TCSlib/Complexity/TuringMachine/Finite
=== 5/57 TCSlib/Complexity/TuringMachine/Oracle
=== 6/57 TCSlib/Complexity/TuringMachine/Simulation
=== 7/57 TCSlib/Complexity/TuringMachine/Sweep
=== 8/57 TCSlib/Complexity/TuringMachine/Composition
=== 9/57 TCSlib/Complexity/TuringMachine/Build/Convention
=== 10/57 TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:135:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:190:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:206:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:226:8: warning: declaration uses 'sorry'
=== 11/57 TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Loop.lean:126:8: warning: declaration uses 'sorry'
=== 12/57 TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
=== 13/57 TCSlib/Complexity/TuringMachine/Robustness/SingleTape
=== 14/57 TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
=== 15/57 TCSlib/Complexity/ClassP/DTIME
=== 16/57 TCSlib/Complexity/ClassP/TimeConstructible
=== 17/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
=== 18/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 19/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 20/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
=== 21/57 TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 22/57 TCSlib/Complexity/ClassP/P
=== 23/57 TCSlib/Complexity/ClassP/ModelInvariance
=== 24/57 TCSlib/Complexity/ClassP/Examples
=== 25/57 TCSlib/Complexity/TuringMachine/Encoding
=== 26/57 TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:66:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:79:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:96:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:113:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:131:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:145:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:173:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:237:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:258:8: warning: declaration uses 'sorry'
=== 27/57 TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 28/57 TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:448:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:454:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:459:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:484:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:490:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:495:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:719:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:821:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 29/57 TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 30/57 TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 31/57 TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 32/57 TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:314:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:337:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:362:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:427:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:434:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:470:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:477:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:487:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:621:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:644:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:659:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:638:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:684:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:761:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:820:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:847:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:889:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:897:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1006:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1106:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1578:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1606:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2278:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 33/57 TCSlib/Complexity/Uncomputability/Computable
=== 34/57 TCSlib/Complexity/Uncomputability/Diagonalization
=== 35/57 TCSlib/Complexity/Uncomputability/Halting
=== 36/57 TCSlib/Complexity/TuringMachine/Nondeterministic
=== 37/57 TCSlib/Complexity/Formulas/CNF
=== 38/57 TCSlib/Complexity/Formulas/CNFEncoding
=== 39/57 TCSlib/Complexity/Formulas/DNF
=== 40/57 TCSlib/Complexity/ClassNP/PolyTime
=== 41/57 TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/NP.lean:359:8: warning: declaration uses 'sorry'
=== 42/57 TCSlib/Complexity/ClassNP/CoNP
=== 43/57 TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:750:16: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/EXP.lean:879:8: warning: declaration uses 'sorry'
=== 44/57 TCSlib/Complexity/ClassNP/Reductions
=== 45/57 TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
=== 46/57 TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:672:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:712:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:722:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:742:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:763:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:774:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:810:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:816:8: warning: declaration uses 'sorry'
=== 47/57 TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:120:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:155:8: warning: declaration uses 'sorry'
=== 48/57 TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/ClassNP/TMSAT.lean:951:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/TMSAT.lean:1140:8: warning: declaration uses 'sorry'
=== 49/57 TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Snapshot.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:192:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:204:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:244:8: warning: declaration uses 'sorry'
=== 50/57 TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
=== 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
=== 52/57 TCSlib/Complexity/TuringMachine
=== 53/57 TCSlib/Complexity/ClassP
=== 54/57 TCSlib/Complexity/Uncomputability
=== 55/57 TCSlib/Complexity/Formulas
=== 56/57 TCSlib/Complexity/CookLevin
=== 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
END_UTC: 2026-10-03T07:12:42Z


## ===== audits/logs/ch1-infra-r2-sweep.log =====

shared infrastructure round 2: verification sweep (57 modules)
START_UTC: 2026-10-03T16:38:22Z
=== 1/57 TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 2/57 TCSlib/Complexity/TuringMachine/Deterministic
=== 3/57 TCSlib/Complexity/TuringMachine/StateRenaming
=== 4/57 TCSlib/Complexity/TuringMachine/Finite
=== 5/57 TCSlib/Complexity/TuringMachine/Oracle
=== 6/57 TCSlib/Complexity/TuringMachine/Simulation
=== 7/57 TCSlib/Complexity/TuringMachine/Sweep
=== 8/57 TCSlib/Complexity/TuringMachine/Composition
=== 9/57 TCSlib/Complexity/TuringMachine/Build/Convention
=== 10/57 TCSlib/Complexity/TuringMachine/Build/Wrappers
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:135:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:190:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:206:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:226:8: warning: declaration uses 'sorry'
=== 11/57 TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Loop.lean:159:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Loop.lean:213:8: warning: declaration uses 'sorry'
=== 12/57 TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
=== 13/57 TCSlib/Complexity/TuringMachine/Robustness/SingleTape
=== 14/57 TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
=== 15/57 TCSlib/Complexity/ClassP/DTIME
=== 16/57 TCSlib/Complexity/ClassP/TimeConstructible
=== 17/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
=== 18/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 19/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 20/57 TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
=== 21/57 TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 22/57 TCSlib/Complexity/ClassP/P
=== 23/57 TCSlib/Complexity/ClassP/ModelInvariance
=== 24/57 TCSlib/Complexity/ClassP/Examples
=== 25/57 TCSlib/Complexity/TuringMachine/Encoding
=== 26/57 TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:72:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:85:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:106:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:124:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:142:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:156:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:171:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:184:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:200:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:237:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:260:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:281:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:318:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:339:8: warning: declaration uses 'sorry'
=== 27/57 TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 28/57 TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:448:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:454:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:459:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:484:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:490:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:495:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:496:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:719:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:821:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:869:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 29/57 TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 30/57 TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
=== 31/57 TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 32/57 TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:314:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:337:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:362:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:427:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:434:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:443:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:470:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:477:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:487:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:621:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:622:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:644:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:659:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:638:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:669:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:684:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:740:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:761:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:820:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:847:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:865:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:889:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:897:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1006:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1106:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1484:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1578:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1583:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1606:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1608:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2278:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
=== 33/57 TCSlib/Complexity/Uncomputability/Computable
=== 34/57 TCSlib/Complexity/Uncomputability/Diagonalization
=== 35/57 TCSlib/Complexity/Uncomputability/Halting
=== 36/57 TCSlib/Complexity/TuringMachine/Nondeterministic
=== 37/57 TCSlib/Complexity/Formulas/CNF
=== 38/57 TCSlib/Complexity/Formulas/CNFEncoding
=== 39/57 TCSlib/Complexity/Formulas/DNF
=== 40/57 TCSlib/Complexity/ClassNP/PolyTime
=== 41/57 TCSlib/Complexity/ClassNP/NP
TCSlib/Complexity/ClassNP/NP.lean:359:8: warning: declaration uses 'sorry'
=== 42/57 TCSlib/Complexity/ClassNP/CoNP
=== 43/57 TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:750:16: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/EXP.lean:879:8: warning: declaration uses 'sorry'
=== 44/57 TCSlib/Complexity/ClassNP/Reductions
=== 45/57 TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
=== 46/57 TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:672:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:712:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:722:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:742:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:763:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:774:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:810:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Nondeterminism.lean:816:8: warning: declaration uses 'sorry'
=== 47/57 TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:120:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/SAT.lean:155:8: warning: declaration uses 'sorry'
=== 48/57 TCSlib/Complexity/ClassNP/TMSAT
TCSlib/Complexity/ClassNP/TMSAT.lean:951:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/TMSAT.lean:1140:8: warning: declaration uses 'sorry'
=== 49/57 TCSlib/Complexity/CookLevin/Snapshot
TCSlib/Complexity/CookLevin/Snapshot.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:192:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:204:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Snapshot.lean:244:8: warning: declaration uses 'sorry'
=== 50/57 TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:82:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:212:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:219:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:228:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
=== 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
=== 52/57 TCSlib/Complexity/TuringMachine
=== 53/57 TCSlib/Complexity/ClassP
=== 54/57 TCSlib/Complexity/Uncomputability
=== 55/57 TCSlib/Complexity/Formulas
=== 56/57 TCSlib/Complexity/CookLevin
=== 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
END_UTC: 2026-10-03T16:39:48Z


## ===== audits/logs/ch1-infra-r2-axioms.log =====

shared infrastructure round 2: axiom attestation at the r2 tree
UTC: 2026-10-03T16:40:00Z
'Turing.timed_universal_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.timed_universal_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.timed_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_effectiveMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.HALT_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPHard' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPComplete' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
ROOTS Turing.timed_universal_concrete: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Turing.timed_universal: []
ROOTS Complexity.TMSAT_mem_NP: [Complexity.TMSAT_mem_NP]
ROOTS Complexity.TMSAT_NPHard: [Complexity.TMSAT_NPHard]
ROOTS Complexity.TMSAT_NPComplete: [Complexity.TMSAT_NPHard, Complexity.TMSAT_mem_NP]
ROOTS Complexity.NP_subset_EXP: [Complexity.enumMachine_contracts]
ROOTS Complexity.HALT_NPHard: [Complexity.enumMachine_contracts]
BRIDGE AUDIT PASS: the export and the discharged bridge are admission-free; TMSAT roots shrank exactly to their D-sites; headline and epoch-2 regressions unchanged.
---
'Turing.timed_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_effectiveMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.HALT_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.initCfg_ofWords' depends on axioms: [propext, Quot.sound]
'Turing.Cfg.ofWords_workTapes' depends on axioms: [propext]
'Turing.capture_run' depends on axioms: [propext, sorryAx, Quot.sound]
'Turing.FinTM.redirectTM_computes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_live' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_cond' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.loop_run' depends on axioms: [propext, sorryAx, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
lean exit: 0


## ===== audits/logs/ch1-infra-r2-lint.log =====

WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               122 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     253 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               344 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 235 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines; 13 public / 49 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    651 lines; 6 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  403 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       481 lines; 19 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         257 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1100 lines; 1 public / 73 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               248 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         517 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   600 lines; 1 public / 50 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines; 2 public / 53 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     919 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2901 lines; 4 public / 130 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations

style_lint: 0 FAIL, 6 WARN over 28 files
---
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean           1206 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassNP/CoNP.lean            165 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/EXP.lean             882 lines > target 600
INFO  TCSlib/Complexity/ClassNP/EXP.lean             882 lines; 6 public / 40 private declarations
INFO  TCSlib/Complexity/ClassNP/NP.lean              382 lines; 3 public / 18 private declarations
INFO  TCSlib/Complexity/ClassNP/NTIME.lean           222 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean  819 lines > target 600
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean  819 lines; 8 public / 32 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTime.lean        162 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/Reductions.lean      477 lines; 10 public / 16 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean             158 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean           1206 lines; 6 public / 40 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean       133 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 1 WARN over 10 files
