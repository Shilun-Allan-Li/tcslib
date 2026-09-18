# External audit pack — Fill campaign, Epoch 4 (final fill round + campaign closure)

Audits commit `fd7bb18e` on `complexity/arora-barak-ch1`. Since the epoch-3
resolutions (`audits/epoch3-resolutions.md`), three things happened. **(a)**
The **epoch-3→4 merge refactor** (commit `ff2161e4`): the three oversized fill
files were mechanically split into twelve modules — `Encoding` (481, pre-fill
layout restored) + `CodeParser` (790) + `MathlibBridge` (1100, quarantining the
`TMToPartrec` import and holding `exists_effectiveMachineCode`);
`UniversalStartup` (591) + `UniversalInterpreter` (1020) + `UniversalBlock`
(794) + `Universal` (208, statements only); `ObliviousSchedule` (688, incl. the
relocated public `FinTM.Oblivious` def) + `ObliviousCandidate` (1127) +
`ObliviousSetup` (1102) + `ObliviousLedger` (219) + `Oblivious` (1147). Content
is **verbatim from the audited fills**: 151 forced `private`→`public`
visibility flips and exactly **one** code change (a single `rfl` added in the
private `dataCfg_backward_step`, forced by Lean's per-module `match`-auxiliary
minting — the same constraint that fixed one Universal cut point; both recorded
in module docstrings). Execution reports in `audits/epoch3-split-reports/`.
**(b)** The **epoch-4A fill** (agent commit `37d70522`, from
`briefs/epoch4-batchA.md`): `Turing.timed_universal` proved — the campaign's
last sorry. **(c)** Campaign-closure records in the plan. Record findings in
`audits/epoch4-findings.md`.

The campaign standing: **21 of 21 audited sorries proved. The tree contains no
`sorry` and no theorem depends on `sorryAx`.** [AB09] Chapter 1's critical path
— Theorem 1.9 (evaluator, quadratic corollary, and time-bounded form),
Theorem 1.10, Theorem 1.11, the effective-representation existence
(Exercise 1.11 strengthened), and Exercise 1.5 — is fully machine-checked.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Statement freeze / drift (campaign closure).** Tree-wide public-name
   comparison between the epoch-3 audited commit (`b519a004`) and this commit:
   227 public declarations then, 378 now — **zero names lost, exactly 151
   gained**, and the gained set is exactly the recorded refactor promotions
   (21 batch-A incl. 8 pre-fill `Encoding` privates / 53 batch-B / 77
   batch-C); the epoch-4A fill added **zero** public declarations (its 130 new
   declarations are all private). Per split, the maintainer ran both the
   comment-stripped **multiset** and the **ordered declaration-sequence**
   comparison (the epoch-3 finding-7 methodology): B and C sequences identical
   (107 / 240 declarations), A identical modulo the byte-verified
   `exists_codeTM` relocation; the only line of Lean code changed anywhere in
   the refactor is the one `rfl` above. The epoch-4A fill span removes exactly
   **one** line — the final `sorry` — and the three `Universal.lean` public
   theorem headers are byte-identical across the span. Three public
   declarations changed *file* (never name, statement, or namespace):
   `exists_effectiveMachineCode` (→ `MathlibBridge`), `FinTM.Oblivious`
   (→ `ObliviousSchedule`), `exists_codeTM` (restored to its pre-fill position
   in `Encoding`).
2. **Elaboration.** Full **34-module** fresh-olean sweep via the strengthened
   `scripts/lean_check_tree.sh`, Lean 4.25.0 / mathlib `029db123ddaa`: zero
   `error:` lines, zero gate failures, and — for the first time in the
   campaign — **zero `declaration uses 'sorry'` warnings**. Run twice by the
   maintainer at this tree content (post-refactor and post-fill); the 4A
   agent's own sweep agrees.
3. **Axiom footprints** (`#print axioms`, maintainer-run on the integrated
   tree):

   ```text
   'Turing.universal'                            [propext, Classical.choice, Quot.sound]
   'Turing.universal_quadratic'                  [propext, Classical.choice, Quot.sound]
   'Turing.timed_universal'                      [propext, Classical.choice, Quot.sound]
   'Turing.exists_effectiveMachineCode'          [propext, Classical.choice, Quot.sound]
   'Complexity.oblivious_of_mem_DTIME'           [propext, Classical.choice, Quot.sound]
   'Complexity.UC_not_computable'                [propext, Classical.choice, Quot.sound]
   'Complexity.UC_computable_of_HALT_computable' [propext, Classical.choice, Quot.sound]
   'Complexity.HALT_not_computable'              [propext, Classical.choice, Quot.sound]
   ```

   **No admission of any kind remains.**
4. **Soundness scan** (programmatic, both spans). Fill span: no added `axiom`,
   `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, or `set_option`;
   one added import (`Mathlib.Tactic.FinCases`); one kernel-checked `decide`.
   Refactor span: import *redistribution* plus `Mathlib.Data.Nat.Bits` where
   transitivity was lost, all other Mathlib imports pre-existing at their new
   locations; the `TMToPartrec` cone is now confined to `MathlibBridge.lean`.
5. **Policy conformance** (`scripts/style_lint.py`). Campaign tree: zero FAIL.
   Six size WARNs, all with recorded justifications (plan decision log):
   `Universal.lean` **2831** — the 4A fill's escalation: the brief forbade
   splitting and forbade touching the audited infrastructure modules, and
   ~1100 of the new lines are stopped-interpreter administrative copies forced
   by per-module `match` auxiliaries, with the agent's three shared-lemma
   generalizations recorded as the factoring path; `MathlibBridge` 1100 (the
   single foreign-trust quarantine, kept whole); `UniversalInterpreter` 1020
   (cut fixed by matcher identity); `ObliviousCandidate` 1127 /
   `ObliviousSetup` 1102 / `Oblivious` 1147 (interleaved-layer seams). Legacy
   `NPReductions/*` FAILs remain out of scope.
6. **Delivery provenance.** One zip per the standardized contents; SHA256
   manifest verified; base verified as `ff2161e4`; flat source, patch, and
   bundle mutually consistent; the agent's sweep and axiom logs agree with the
   maintainer's independent runs. Report preserved in
   `audits/epoch4-agent-reports/batchA.md`.
7. **Human-reserved items.** Plan §5's two open design questions (the 3A
   Mathlib bridge's placement; the 3B interpreter architecture) **remain
   open**; the refactor implemented the module quarantine that question 1
   contemplates without disposing of it. As in epoch 3: audit the
   constructions' *correctness*; their design disposition is a human decision.

## What was filled / new surface

| Item | Content | New declarations |
|---|---|---|
| 4A (`Universal.lean`) | `timed_universal` proved: the deadline interpreter `timedUniversalTM` — six lanes (table, state, simulated work, boundary marker, clock, output buffer), outer-pair parsing that stores the clock and canonizes **only `α`**, lane-5 output buffering with a single flush, one fixed-width borrow per simulated transition, halt interception via a live `emitStart` state, and the realized `α`-only constant `C = S + B + 14` with `S = 3A + K + L + 2h + 2q + 16` (startup) and `B = 3L + 5N + 20` (the untimed block bound) | 130, all private |
| Merge refactor | No new mathematics: 151 visibility flips of audited fill content into 9 new modules (each flip forced by a cross-module reference; every flipped declaration carries a statement-prose docstring, 7 minimal ones added in `CodeParser`) | 151 promotions |

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket approval;
tactic scripts are Lean-checked and axiom-audited — out of scope). Priorities:

1. **The timed fill — the round's only new mathematics.** Verify the five
   binding obligations (epoch-3 finding 8) against the delivered lemmas:
   (i) clock/code separation — `timed_input_layout` / `timedPrefix_*` /
   `timedCanon_*`: the canonizer receives exactly `α`, never the
   clock-carrying payload; (ii) buffering — `timedAction` suppresses native
   output onto lane 5, real output empty until `timed_flush` (success) or
   `timed_clock_timeout` (`[false]` exactly); (iii) one borrow per source
   transition — `timedBorrow_value/_length`, `timed_clock_success`;
   (iv) halt interception — a native halted successor maps to the live
   `emitStart` state so the **final transition's emission** is captured before
   the flush; (v) boundaries — deadline-inclusive success at exactly `t`, and
   `t = 0` (`Nat.bits 0 = []`, separators still parsed, timeout with every
   captured emission discarded). Re-sum the ledger: startup `4w + S`, per-step
   `B + 2w + 4`, the induction bound `(B + 2w + 8)(r + 1) + 2ℓ`, and
   `4w + S + (B + 2w + 8)(t + 1) ≤ (S + B + 14)(t + 1)²` — every term
   `α`-only.
2. **The timeout clause on divergent sources.** The second clause quantifies
   over *all* sources failing to halt by `t` — including machines that never
   halt. Verify the induction reaches the underflow branch and the real halt
   with `[false]` within budget for a source that runs forever, and that
   nothing in the argument assumes eventual source halting.
3. **Merge-refactor conformance.** Verify attestation 1's methodology and
   claims from the attached sources and the public GitHub comparisons
   ([refactor span](https://github.com/Shilun-Allan-Li/tcslib/compare/2832663b...ff2161e4),
   [fill span](https://github.com/Shilun-Allan-Li/tcslib/compare/e726238f...fd7bb18e)):
   the 151 promotions carry audited content unchanged, the single `rfl` is
   what it claims, the three relocations preserved statements byte-for-byte,
   and the redistributed imports match the modules' needs.
4. **Statement identity across gates**: confirm the eight headline theorem
   statements are the audited ones (they were byte-compared maintainer-side at
   each integration; challenge from the sources).
5. **Campaign-closure sanity**: no `sorry` token anywhere in the 34 modules;
   no new axiom or bypass mechanism; the escalations and both open design
   questions accurately recorded.
6. Assess attestations 1-7.

## Specific questions

1. At `t = 0` with a source that halts *at time 1* on `x`: confirm the timeout
   clause applies (no output witnesses halting within 0), the interpreter
   performs its stopped lookup without applying the action, and emits exactly
   `[false]` — and that the success clause is vacuous rather than violated.
2. A source whose **final** transition (the `t`-th) both halts and emits:
   confirm the emission reaches the buffer before `timed_flush`, so the
   output is `true :: output` with the complete output.
3. The empty code `α = []` under the timed wrapper (for the concrete 3A
   scheme, the 84-bit fallback): confirm startup parses
   `pairEncode (pairEncode (Nat.bits t) []) x` correctly (clock bits doubled
   twice, empty code, verbatim `x`) and the constant `C` is finite and
   `α`-only.
4. `x = []` with positive `t`: the virtual input boundary (inherited marker
   machinery) under the timed wrapper — confirm the empty-suffix case is
   covered by the reused startup lemmas with the outer payload as prefix
   parameter.
5. Buffer length vs budget: the flush costs `2ℓ + 3` with `ℓ ≤ t` claimed via
   per-step accounting (`MultiTapeTM.step_output`). Confirm a source that
   emits on *every* step (including the halting one) stays within the ledger.
6. The `timedCut_*` "stopped controller" is proof infrastructure, not the
   delivered machine: confirm no stopped-controller behavior leaks into
   `timedUniversalTM`'s definition, and the replay lemma (`timed_replay`)
   transports only proved behavior.

## Scope

| Item | Where |
|---|---|
| Files under audit | `Universal.lean` (the fill: 130 new privates + the three public statements), the nine new refactor modules + three residuals (content verbatim from audited fills; audit the *split conformance*, not a re-audit of audited mathematics); all 34 modules attached |
| Source text | Arora & Barak 2009, §1.4.1 (the time-bounded universal machine, Figure 1.6; PDF pp. 46-48) |
| Context | `AroraBarakChapter1Plan.md` (§5 open design questions; decision log), `policy.md`, `audits/epoch3-{findings,resolutions}.md`, `audits/epoch3-split-reports/`, `briefs/epoch4-batchA.md`, `audits/epoch4-agent-reports/batchA.md` |
| Out of scope | tactic proofs; statements confirmed in closed rounds beyond the freeze check; disposition of the two human-reserved design questions; legacy `NPReductions/*` style findings |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
