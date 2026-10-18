# Chapter 2, epoch 3, batch D — COMPLETE

- Target: `Complexity.TAUTOLOGY_mem_coNP`, proved with no admitted dependencies.
- Working branch: `fill/ch2-e3-D`.
- Required and actual base: `b55180a8bb38b94427e75e63630aa6eab5fd6e95`.
- Delivery commit: `2a432c88fd35a3b1b2bf4f14bb8396b1f2726701`.
- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- The brief was read at branch tip `3293de776053bf755a89c16c5cfbcc7f7d3b8501`,
  whose only successor content was the E3 briefs; work branched directly from
  the brief's required base. No rebase, remote push, or pull request.
- Only modified repository file:
  `TCSlib/Complexity/ClassNP/Tautology.lean`.
- Full source: **1278 lines, 62,104 UTF-8 bytes**.
- Source SHA-256: `54040a2dc1092763b87c8bc26f3be7abdc3e8b9cb38f077b91e6c20d8ccc2e56`.

## Completed obligations

| Obligation | Discharging declarations / evidence |
|---|---|
| Private DNF congruence bridge | `taut_eval_congr`, using `taut_dual_dual`, `taut_numVars_dual`, and the existing CNF congruence and De Morgan theorems |
| Exact certificate parameters `(1,1)` | `taut_certificate_equiv`, `taut_verifier_append`, `taut_membership_of_verifier` |
| Unique odd split; even rejection including empty total input | `taut_split_some`, `taut_split_exists`, `taut_verifier_even`, P10 at `(1,1)`, `taut_machine_empty`, `taut_machine_split` |
| Complete syntax pass before evaluation | `taut_syntax_parse` equates the six-state scan with `CNF.parse`; `taut_syntax_run` realizes it on native paired input; `taut_evaluation_start` only enters evaluation after syntax success |
| Exact successful parse, including trailing-input discipline | `taut_parseLit_shape`, `taut_parseClause_shape`, `taut_parseClauses_shape`, `taut_parse_shape` |
| Assignment copy and sequential walk | `taut_copy_run`, `taut_work_rewind`, `taut_unary_run`, `taut_literal_run`, `taut_literal_lt` |
| Every term must fail for acceptance | `taut_clause_run` accumulates conjunction, `taut_formula_run` rejects upon a true term and accepts only after all terms fail |
| Empty term rejects; empty DNF accepts | The nil case of `taut_clause_run` and the nil case of `taut_formula_run`, respectively |
| Malformed-string equivalence | `taut_malformed` proves complement membership and acceptance for every correctly sized certificate; `taut_machine_malformed` proves the native accepting run for every certificate |
| Single buffered verdict | Only `tautTM`'s `verdict` state emits; `taut_verdict` proves that transition. Every phase endpoint in the native run lemmas has empty output before the verdict; `taut_comp_on_image` captures the split output |
| Native totality on all preprocessor outputs | `taut_machine_pair` and `taut_machine_empty`, assembled by `taut_machine_split` |
| Polynomial-time verifier and final membership | `taut_verifier_mem_P`, followed by `taut_membership_of_verifier` |

The complement verifier computes **the negation of `evalDNF`**. The coNP
wrapper is a separate use of the definition of coNP; these two polarity
steps are not conflated. On malformed formula strings, decoding gives the
empty DNF, whose value is false, so the complement verifier accepts.

The machine is independent of batch 3B. It consumes only the pinned,
previously proved library and formula APIs. No SAT membership, SAT
reduction, Cook–Levin hardness, or completeness admission enters its
kernel dependency closure. `TAUTOLOGY_coNPComplete` retains its original
`sorry` byte for byte.

## Runtime ledger

All bounds are proved for native transitions, with integer work-head
positions and sequential reads. On a pair containing a valid formula:

1. Syntax consumes exactly `2*|x|+2` transitions, including the separator.
2. Copy and both rewinds enter evaluation within `4*(|pairEncode x u|+2)`
   transitions, including the syntax pass.
3. A literal at index `v` takes exactly `3*v+7` transitions. Its
   serialization has length `v+3`, so this is at most three times that
   length. The `v+1` work-rewind transitions are charged on every call.
4. A term takes at most three times its serialized length. A formula,
   including the verdict, takes at most `3*|serialize φ|+1` transitions.
5. `taut_machine_pair` bounds the entire native verifier by
   `10*(|pairEncode x u|+1)`. On P10's actual image,
   `taut_machine_split` bounds it by `40*(n+1)`.
6. P10 supplies one fixed constant `A` and time `A*(n+1)^3`.
   Buffered composition gives
   `2*A*(n+1)^3 + 40*(n+1) + 2 ≤ (2*A+42)*(n+1)^3`.

The second-stage budget is explicitly indexed by the original input
length. No arbitrary time function is evaluated at an inflated
intermediate-length bound.

## Verification

- **Fresh sweep: 57/57; exit 0; zero `error:` lines.** Each invocation
  deleted its prior output before checking and required a fresh olean.
  The final run used a newly created `.lake/e3d-final-oleans` tree.
- Whole-sweep admissions: **20**, down from the pinned base's 21 by exactly
  this target. In the owned source the only remaining admission is
  `TAUTOLOGY_coNPComplete`.
- Final target axiom print:

  ```text
  'Complexity.TAUTOLOGY_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound]
  TARGET ROOTS Complexity.TAUTOLOGY_mem_coNP: []
  ```

- The checked-environment traversal follows declaration types, opaque
  values, and inductive constructors. It checks **333 owned kernel
  declarations**, including all **329 private/generated declarations**;
  their combined admission roots are empty and their only axiom constants
  are the standard triple. The separately checked completeness theorem
  has exactly its own unchanged admission root.
- The kernel public inventory is exactly the original five names:
  `coNPHard`, `coNPComplete`, `TAUTOLOGY`, `TAUTOLOGY_mem_coNP`,
  `TAUTOLOGY_coNPComplete`. Generated equality instances and equation
  helpers remain private; there is no added public surface.
- `verify-source.py` reconstructs the original file **byte for byte** by
  removing the flagged private-helper block and the two precise imports,
  then restoring only the target's original proof placeholder. This
  verifies all original docstrings, definitions, signatures, declaration
  order, and the untouched completeness body together.
- Two precise imports were added: `Build.Primitives` and
  `Mathlib.Data.Sigma.Basic`. The original option headers are unchanged.
  A local `synthInstance.maxSize` setting within the private control-state
  equality instance only accommodates its finite sum representation.
- `git diff --check`: pass. The source diff contains 1,146 insertions and
  one deletion, solely in the owned file.
- ClassNP style lint: **0 FAIL, 4 WARN**. Three warnings are unchanged
  predecessor file-size warnings; the new owned-file size warning is
  justified below. The owned module emits only its expected out-of-scope
  admission warning during Lean verification.
- Bundle verification passed. Applying the format-patch series to a
  separate index loaded from the pinned base reproduces the delivery
  commit's exact tree. The working branch and working tree are verified
  as `fill/ch2-e3-D` and clean.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:234:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1275:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
PASS: 57/57 modules; every check required exit 0, no error diagnostics, and a fresh olean.
```

The environment and cache-recovery details are in `ENVIRONMENT.md`.
`verify-sweep.sh`, `verify-axioms.sh`, `ClosureAxioms.lean`, and
`verify-source.py` make the checks reproducible without editing repository
verification scripts.

## Scope and size disposition

**Statement or shared-lemma escalations: none.** No frozen statement was
altered, no out-of-scope admission was filled, and no new admission was
introduced. All 68 source additions are private and listed below.

**Size exception / deferred modularization requested at integration:** the
owned file is 1278 lines, above the policy's 1,000-line
threshold. The native controller, indexed configurations, and successive
phase proofs form one dependent private family. Keeping that family
together honors the brief's single-file ownership and private-only surface.
A later split should be coordinated by the maintainer under the existing
D7 discipline, preserving private dependencies or separately reviewing any
visibility change. This report records the positive justification; no
unapproved split or public promotion is included.

## Archive and integration

The archive is **flat**: `SHA256SUMS`, this report, the full source, one
format-patch, the incremental git bundle, and all evidence files are at
its root. The source filename `Tautology.lean` maps to
`TCSlib/Complexity/ClassNP/Tautology.lean`. No build caches are included.

The bundle contains branch `fill/ch2-e3-D` at the delivery commit and requires
the pinned base as its prerequisite. Integrate the single patch with the
campaign's usual `git am -3` route from that base. Verify `SHA256SUMS`
before integrating. The copied brief is included for review; it is not a
repository change in this delivery.

## Every new source declaration

All names below are private members of namespace `Complexity`.

| Kind | Name |
|---|---|
| `lemma` | `taut_dual_dual` |
| `lemma` | `taut_numVars_dual` |
| `lemma` | `taut_eval_congr` |
| `def` | `tautAssignment` |
| `lemma` | `taut_certificate_equiv` |
| `lemma` | `taut_split_some` |
| `lemma` | `taut_split_exists` |
| `def` | `tautVerifierBit` |
| `def` | `tautVerifier` |
| `lemma` | `taut_verifier_append` |
| `lemma` | `taut_verifier_even` |
| `lemma` | `taut_malformed` |
| `lemma` | `taut_membership_of_verifier` |
| `inductive` | `TautSyntax` |
| `instance` | `tautSyntaxDecidableEq` |
| `instance` | `tautSyntaxFintype` |
| `def` | `tautSyntaxStep` |
| `def` | `tautSyntaxAccept` |
| `lemma` | `taut_syntax_cons` |
| `lemma` | `taut_syntax_bad` |
| `lemma` | `taut_syntax_done` |
| `lemma` | `taut_takeTrues_shape` |
| `lemma` | `taut_parseLit_shape` |
| `lemma` | `taut_parseClause_shape` |
| `lemma` | `taut_parseClauses_shape` |
| `lemma` | `taut_parse_shape` |
| `lemma` | `taut_syntax_unary` |
| `lemma` | `taut_syntax_literal` |
| `lemma` | `taut_syntax_clause` |
| `lemma` | `taut_syntax_formula` |
| `lemma` | `taut_syntax_parse` |
| `inductive` | `TautEval` |
| `instance` | `tautEvalDecidableEq` |
| `instance` | `tautEvalFintype` |
| `inductive` | `TautControl` |
| `instance` | `tautControlDecidableEq` |
| `instance` | `tautControlFintype` |
| `def` | `tautMove` |
| `def` | `tautEvalAction` |
| `def` | `tautTM` |
| `def` | `tautCfg` |
| `lemma` | `taut_read` |
| `lemma` | `taut_move_right` |
| `lemma` | `taut_move_stay` |
| `lemma` | `taut_syntax_double` |
| `lemma` | `taut_syntax_separator` |
| `lemma` | `taut_syntax_run` |
| `lemma` | `taut_init` |
| `lemma` | `taut_verdict` |
| `lemma` | `taut_machine_malformed` |
| `lemma` | `taut_machine_empty` |
| `lemma` | `taut_copy_run` |
| `lemma` | `taut_work_rewind` |
| `lemma` | `taut_evaluation_start` |
| `lemma` | `taut_eval_double` |
| `lemma` | `taut_pair_append` |
| `lemma` | `taut_double_length` |
| `lemma` | `taut_unary_run` |
| `lemma` | `taut_literal_run` |
| `lemma` | `taut_clause_run` |
| `lemma` | `taut_formula_run` |
| `lemma` | `taut_le_max` |
| `lemma` | `taut_literal_lt` |
| `lemma` | `taut_machine_pair` |
| `def` | `tautSplit` |
| `lemma` | `taut_machine_split` |
| `lemma` | `taut_comp_on_image` |
| `lemma` | `taut_verifier_mem_P` |

## Notation glossary

`x`: formula string; `u`: assignment certificate, of length `|x|+1`;
`n`: length of the original concatenated verifier input; `v`: literal
variable index; `φ`: parsed formula; `A`: the fixed split-machine time
constant; `|·|`: list length.
