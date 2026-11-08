# Independent construction proof fill

The combined statement audit passes 0 blockers, 0 majors, 1 documentation minor
and 4 notes. Its F01 comment is corrected and checked separately. This fill
completes **31 independent obligations in seven modules**, leaving **70 owned
admissions**. It does not use any pending shared reader or counted-loop exception.

| Item | Identity |
|---|---|
| Own worktree | `tcslib-lwe-sis-construction-statements` |
| Branch / draft PR | `cryptography/lwe-sis-construction-statements` / #250 |
| Central target | `cryptography/lwe-sis-constructions` |
| Statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Passed gate plus doc-repair baseline | `13aff4d33d282ccaed2727af3febc0ebddeba0e5` |
| Filled Lean/root | `f293b63200ee3c6de6e709925f67c4d60fdc7b4a` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

| Slice | Filled proofs |
|---|---:|
| Dyadic scalar/vector/matrix bijections, laws and round trips | 9 |
| Actual bit-noise probability, support, symmetry and mean | 4 |
| Common-secret sampling laws and acceptance | 3 |
| Regev every-coin PKE correctness | 4 |
| Direct generators: basic, encoded and flat representations | 11 |
| **Total** | **31** |

A final fresh serial 144-module sweep passes in 303.792 seconds. The final axiom
probe records 53.149 seconds. All selected targets have only standard axioms;
exactly the other seventy source obligations retain `sorryAx`. The complete
inventory has 589 constants, including fourteen new compiler auxiliaries. Two
earlier congruence helpers are now emitted in their owning module; their exact
types and axiom sets are preserved. Separate native probes compare all 575 prior
level-parameter/type-expression representations exactly. Baseline objects are
this same chat's preserved audited objects, not a new historical rebuild.

All 220 source declarations, 62 earlier closed readers, definitions, signatures,
imports, options and attributes remain fixed. Scope, provenance and execution
limits are in `REPORT.md`; raw checks, freeze, type and axiom inventories are under
`evidence/`. Whole-library root elaboration, source-policy closure and final
primitive-security interfaces remain unclaimed. New proof work adds no export edit.

The missing random-bit/probability readers and loop catalogue/host-gate disposition
remain unapplied proposals under the statement gate and continuation records.
Affected fills stay paused. Other remaining admissions include later independent
work too; this fill does not claim they are all blocked.

Codex is preselected by the user. `build_review.py` prepares one immutable owned
exchange packet, and the client `publish_review.py` updates only draft #250 and
that packet before printing the kickoff. The user dispatches; the auditor reads
GitHub and returns Markdown in chat. No ZIP, automatic dispatch or merge occurs.

**Not yet clear to merge — this proof gate, seventy remaining admissions,
shared-owner dispositions, source-policy work, landing checks and user approval
remain.**
