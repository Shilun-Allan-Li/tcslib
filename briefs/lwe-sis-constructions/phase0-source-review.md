# Phase 0 initial source review

This is an internal source review, not an external gate or a Lean execution attestation.

## Drafted surface

| Module | Surface |
|---|---|
| `LWE/Noise` | Scalar integer noise from finite nonempty seeds; support-bound predicate |
| `LWE/Basic` | Numeric parameters; nonzero-modulus instance; common-secret sample map |
| `LWE/Experiments` | Concrete advantage against the independent uniform comparison |
| `SIS/Basic` | Numeric parameters; integer nonzero/squared-norm/modular-kernel relation |
| `SIS/Experiments` | Uniform-matrix success experiment with optional integer-vector output |
| `LWE`, `SIS` | New facades only; no existing facade or root export changed |

## Source conclusions

1. The matrix and secret are different components of a uniform product seed. There is
   one secret component for all sample rows. Scalar error seeds form a function indexed
   by the rows, hence the intended independent product under uniform sampling.
2. The noise law is determined by seed multiplicities. No claim is made that its support
   is sampled uniformly, or that an infinite Gaussian is represented exactly. Machine
   efficiency and exact/approximate sampling contracts are still to be supplied.
3. The ideal comparison sampler is the identity on the *whole* matrix-and-value space.
   Uniformly sampling this product gives independent uniform components, with the same
   public output type as the real experiment.
4. The numeric bundles enforce modulus at least two. Zero dimensions and zero sample
   counts are permitted for boundary checks. Neither a hardness assumption nor solution
   existence follows from the numeric bundles; all consumer nonvacuity conditions remain
   explicit obligations.
5. SIS nonzeroness is over integer vectors, prior to reduction modulo the modulus.
   The relation intentionally accepts a modulus multiple when the norm bound allows it;
   consumer parameter restrictions must exclude this trivial regime. Testing residue
   nonzeroness instead would misstate SIS.
6. The SIS norm bound is a bound on the sum of integer coordinate squares. It is not
   silently an unsquared Euclidean radius. The solver's `none` output is unsuccessful.
7. All current proof terms are definitional readers or the elementary nonzero-modulus
   instance. There are no security proofs, nontrivial fills, `sorry` declarations, new
   axioms, custom machines, or copies of existing proved material in the draft source.
   Native elaboration and elaborated axiom prints have not been performed.

## Lightweight checks observed

- `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/LWE`: zero FAIL/WARN
  over the three mathematical modules.
- `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/SIS`: zero FAIL/WARN
  over the two mathematical modules.
- Independent exact finite calculations passed as recorded in `finite-model-results.json`.
  Their executable is `check_finite_models.py`. They do not execute the Lean definitions.
- Lean version inspection reports 4.25.0. Native module checks remain unexecuted.

## Remaining foundation work

The phase-0 gate still needs canonical modular/integer encodings, faithful-decoding
statements, polynomial parameter schedules, efficient-sampling contracts, and the
nonuniform-PPT versions of decisional LWE and SIS hardness. The draft concrete advantage
and success functions are not those asymptotic hardness assumptions.

An isolated source snapshot for Mathlib and its required upstream packages was exported
from tracked source at the exact manifest revisions into this worktree's own `.lake/`.
No build objects were copied, no cache/native jobs were launched, and no source package
in the other checkout was modified. The local source-export manifest is
`.lake/source-exports.json`; it is not an elaboration record.

Before native/cache verification, establish the current state of other jobs. The
execution sandbox denies process inspection. After that constraint is resolved, fetch
only the Mathlib roots required by the transitive imports, produce fresh dependencies
and module oleans in this worktree's own tree, and check each module through the
repository script. Do not describe these drafts as checked in the meantime.

## Shared-file and delivery status

The existing shared owner APIs, existing facades, root exports, dependency pins, and
other worktrees are unchanged by this branch. No campaign/exchange branch was pushed.
The proposed root import diff is in the plan and will be a separate commit after its
modules are checked. No audit vendor has been selected and no external job dispatched.

**Not yet clear to merge — source drafts and finite checks exist; native verification,
remaining foundation statements, exact source archives, and an external gate are pending.**
