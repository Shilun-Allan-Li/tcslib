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
