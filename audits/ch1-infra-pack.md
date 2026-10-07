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
