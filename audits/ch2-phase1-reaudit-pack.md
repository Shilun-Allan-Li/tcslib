# External audit pack — Chapter 2, Phase 1, round 2 (re-audit of the repairs)

Audits commit `8660c416` on `complexity/arora-barak-ch1`. Round 1
(`audits/ch2-phase1-pack.md` → `audits/ch2-phase1-findings.md`, audited at
`ab82bb6a`) returned **3 blockers, 3 majors, 3 minors, 3 notes**; all were
accepted and repaired in this commit, largely along the auditor's own proposed
constructions. This round re-audits the repaired statements and sketches. The
gate closes only on zero blockers/majors here (the Chapter-1 phase-3
precedent: blocker rounds get a clean re-audit before any fill). Record
findings in `audits/ch2-phase1-reaudit-findings.md`.

## Resolution of the round-1 findings (verify each)

| Round-1 finding | Resolution in `8660c416` |
|---|---|
| 1 blocker — `NP`/`NEXP` length functions constrained only numerically (Argument A: length arithmetic decides any `A`) | `NP`, `coNP`'s ∀-characterization, and `NEXP` now quantify over **explicit effective length formulas**: certificates of length exactly `C·(n+1)^c` (resp. `C·2^((n+1)^c)`), with `C, c` quantified as naturals — never an abstract function. `PolyBound`/`ExpBound` survive as numerical helpers only, with docstrings stating exactly that (and why) |
| 2 blocker — Exercise-2.1 equivalence false (Argument B: bounded length + plain concatenation forces `V ⊆ L`; padding fix checked the majorant, not the original bound) | `mem_NP_iff_exists_length_le` restated: the bounded side pairs its inputs with `Turing.pairEncode x u`; the (⇐) sketch's verifier recovers the split from the strictly monotone explicit length (now computable), rejects marker-free certificate regions, and checks the stripped certificate against the **original** explicit bound `C(n+1)^c` — checkable precisely because the bound is now a formula |
| 3 blocker — `HALT_NPHard` false (Argument D: nothing was NP-hard for the defective class) | Consequence of finding 1; with the repaired `NP` the statement is the standard one. Additionally **generalized to every `Turing.MachineCode`** per note 11 |
| 4 major — `exists_comp_partial` cited for time bounds it does not carry | `compl_mem_P` and `mem_P_of_polyTimeReducible` re-sketched through the timed `computesFunInTime_comp`, with the pointwise decider-to-`ComputesFunInTime` conversion and explicit-budget monotonicity named |
| 5 major — enumerator sketch cited private/inapplicable counter machinery | `NP_subset_EXP` re-sketched: polynomial-evaluation machine, fixed-width increment with overflow detection (private `counterInc` acknowledged as a template, promotion a fill-time decision), input/candidate retention, verifier reset, and a timed loop invariant are all **named obligations**; enumeration is over exactly the definition's length (round-1 question 4 resolved by the repair); budget is the audit's own `a·2^(Q n)(n+Q n+1)^d ≤ 2^(n^e)` estimate |
| 6 major — divergent searcher incompatible with `one_work_tape_binary`'s totality | `HALT_NPHard` re-sketched on the audit's recipe: total decider from the repaired `NP_subset_EXP` → `one_work_tape_binary` (legal) → finite-control modification remembering the emitted bit, halting iff `true`, else a stationary live loop (its run/halting lemma a named obligation) → `exists_codeTM` (no totality hypothesis) → fixed-prefix `pairEncode α ·` machine (`2|α| + |x| + 3` steps, a named new obligation distinct from `pairDiagTM`) |
| 7 minor — composition degree `c·c'` misses `c' = 0` | Sketch uses `max c (c·c')` with the audit's absorption inequality |
| 8 minor — monotonicity misattributions | `PolyBound`'s docstring attributes monotonicity to the majorant only; `EXP_subset_NEXP`'s sketch attributes strict monotonicity to `n + p n` (with `p` nondecreasing, constant at degree 0) |
| 9 minor — stale/nonexistent names | Module docstring now advertises `output_length_le`; `ComputesFunInTime.mono` citation replaced by pointwise `ComputesInTime.mono` |
| 10 note — `V ∈ P` abstraction sound | Retained, with the finding cited in `NP`'s design notes |
| 11 note — hardness generalizes to `MachineCode` | Adopted: `HALT_NPHard (c : MachineCode)`; `HALT_not_mem_NP` stays at `EffectiveMachineCode`, with the pathological-scheme counterexample (a scheme decoding everything to the trivial machine makes `HALT` decidable) recorded in its docstring — mirroring Chapter 1's 1.10/1.11 effectivity split |
| 12 note — root export unverified | **Genuine miss, fixed**: `TCSlib.lean` now imports `TCSlib.Complexity.ClassNP` |

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Scope of the repair commit.** `8660c416` touches exactly: the six
   `ClassNP/` files, `TCSlib.lean` (one import line), the Chapter-2 plan
   (decision-log rows), and adds the round-1 findings file. **Zero Chapter-1
   Lean files touched**; the Chapter-1 tree is bit-identical to the round-1
   audited state, whose full 40-module fresh sweep stands.
2. **Elaboration.** All six `ClassNP/` modules re-gated at `8660c416` (fresh
   oleans, zero `error:` lines); admissions unchanged at exactly **19**, same
   per-file distribution (3/2/4/3/7). Nothing outside `ClassNP/` imports these
   modules except the root `TCSlib.lean`, whose elaboration is the main-branch
   CI's gate (it imports non-campaign trees our check harness does not build);
   the added import line is syntactic surface the auditor can verify directly.
3. **Statement deltas.** Relative to round 1, the *statements* of `NP`,
   `mem_NP_iff_exists_length_le`, `mem_coNP_iff_forall`, `NEXP`, and
   `HALT_NPHard` changed (the repairs); all other 14 statements are unchanged
   (their sketches changed where findings 4-9 required). `PolyBound`/`ExpBound`
   definitions are unchanged (docstrings only).
4. **Policy.** `scripts/style_lint.py`: zero FAIL; six pre-existing Chapter-1
   WARNs unchanged; every sorry keeps its sketch; statement-prose intact on all
   29 public declarations.

## Brief for the auditor

1. **Re-run your own artillery.** Apply Arguments A, B, and D to the repaired
   definitions and confirm each dies — or find the residual. In particular:
   with `C, c` quantified but the formula fixed, is there any remaining channel
   by which the certificate-length *value* can carry input-length-dependent
   information? Is plain concatenation now harmless in the **exact**-length
   form (the repair kept it there, moving to pairing only in the bounded
   form)?
2. **Re-derive the repaired Exercise 2.1** in both directions against the new
   statement: the (⇒) paired verifier (parse, length-check, reassemble,
   consult `V`) and the (⇐) split-then-strip verifier (unique `n` from the
   strictly increasing padded length; original-bound check). Probe `C = 0`,
   `c = 0`, `x = []`, `u = []`, and certificates that are all `false`.
3. **Check the searcher recipe's legality** step by step against the attached
   Chapter-1 API (`one_work_tape_binary`'s exact hypotheses; `exists_codeTM`'s
   lack of totality hypothesis; whether the control modification preserves the
   one-work-tape binary form that `exists_codeTM` needs).
4. **Adjudicate the `MachineCode`/`EffectiveMachineCode` asymmetry**: is
   `HALT_NPHard` really provable at full `MachineCode` generality (the
   reduction uses only `decode_encode` on one fixed code), and is the
   documented pathological-scheme argument for keeping `HALT_not_mem_NP` at
   `EffectiveMachineCode` correct?
5. **Sketch implementability** for the re-sketched proofs (findings 4-6
   repairs): confirm the named obligations are complete — would a fill agent
   hit anything not on the list?
6. Assess attestations 1-4 and the resolution table row by row.

## Specific questions

1. In the repaired `NP`, the quantified `(C, c)` pair varies with `L` but not
   with `x`. Confirm no Argument-A-style selector survives (e.g. via unusual
   `V` exploiting the formula's value mod small numbers — the round-1 mod-3
   trick now applied to a *fixed* formula).
2. `pairEncode x u` doubles the **first** component (`x`), keeping `u`
   verbatim — Chapter 1's code-first convention transplanted. Any issue with
   certificate-side self-delimiting, or should the pairing be `pairEncode u x`?
   (The bounded verifier parses the aligned pair either way; check which order
   the (⇐) construction wants.)
3. Round 1's question-3 answer said direct exact-form normalization works once
   `p` is effective. With the formula now explicit, is
   `mem_NP_iff_exists_length_le` still the right *statement* of Exercise 2.1,
   or should a second, concatenation-based bounded variant with explicit
   formulas also be stated (and would it be true, given Argument B's
   prefix-free obstruction survives the length repair)?
4. The `NP_subset_EXP` budget: confirm `a·2^(Q n)(n + Q n + 1)^d ≤ 2^(n^e)`
   absorbs correctly at small `n` under `DTIME`'s external constant, including
   `Q n = 0` (the `C = 0` class: `V`-membership of `x` alone — one round).
5. `HALT_not_mem_NP`'s docstring argues nonmembership fails at `MachineCode`
   generality via the trivial-machine scheme. Is that pathology *actually* a
   `MachineCode`? (It must satisfy `decode_encode` — decode ∘ encode = id —
   while decoding all non-image strings to the trivial machine. Verify.)
6. The root export: any policy expectation beyond the added import line that
   the campaign harness should track?

## Scope

| Item | Where |
|---|---|
| Files under audit | the six `ClassNP/` files at `8660c416` (statements + sketches), the one-line `TCSlib.lean` change |
| Context | `audits/ch2-phase1-findings.md` (round 1 — your report), `audits/ch2-phase1-pack.md` (round 1 pack), `AroraBarakChapter2Plan.md` (updated decision log), `AroraBarakChapter1Plan.md`, `policy.md`; all 40 modules attached |
| Out of scope | Chapter-1 mathematics; proof tactics (none exist); phase-2/3 design questions |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
