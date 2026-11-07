# Phase 0 internal source review

This is internal review data, not an external gate or a proof of the admitted statements.
Execution evidence is separate, under `gates/00-foundations/evidence/`.

## Reviewed surface

| Modules | Surface |
|---|---|
| `Encoding/Modular` | Fixed-width vectors and row-major matrices; representation obligations |
| `LWE/Noise`, `LWE/Basic` | Finite nonempty noise seeds; one common secret for all rows |
| `LWE/Experiments`, `LWE/Encoding` | Concrete distinguishing experiment and canonical input |
| `LWE/Assumption` | Polynomial input budgets and `DLWEAssumption` against `NUPPT` |
| `SIS/Basic`, `SIS/Experiments` | Integer short-kernel relation and uniform-matrix success |
| `SIS/Encoding`, `SIS/Assumption` | Signed outputs, completeness obligations and `SISAssumption` |
| Three facades | Complete child imports; root additions in a separate commit |

## Conclusions for independent challenge

1. Real LWE seeds have separate matrix, secret and row-noise components. One secret
   serves all rows. Independent row seeds give independent copies of the scalar law.
2. Noise is determined by seed multiplicities, not uniform sampling on its support.
   This expresses finite rational laws, not an exact infinite discrete Gaussian.
   Efficient sampling is separate; exact fair-bit sampling at general moduli needs work.
3. The ideal sampler is the identity on the full matrix/value product. A uniform input
   gives independent uniform components of the right output type. Concrete adversary
   coins are explicitly nonempty.
4. Moduli are at least two. Zero dimensions/sample counts remain permitted for boundary
   checks. These bundles imply neither hardness nor nonvacuity.
5. Polynomial bounds cover actual encoded inputs, with widths large enough for residues.
   DLWE hardness concerns one stored sample-count schedule, not all polynomial schedules.
   Numeric schedules/noise samplers are not asserted uniformly computable.
6. SIS nonzeroness is over integers, before modular reduction. The squared-norm bound is
   explicit. Modulus multiples are accepted when the bound permits them; consumer profiles
   must exclude that trivial regime. Solution existence and LWE/SIS bridges are not asserted.
7. SIS machine output has an exact prescribed length. Negative zero represents zero;
   output-string uniqueness is unnecessary. The family conservatively requires its squared
   norm bound to fit the magnitude width. Decoder completeness is an admitted theorem,
   rather than a correctness hypothesis hidden inside the assumption.
8. Internal mathematical review found no defect in the 14 representation statements.
   They still have `sorry` bodies. No construction, sampler machine, private host or copy
   of existing proved material was introduced.

## Execution and limits

An early check exposed a missing matrix finiteness instance; the precise
`Mathlib.Data.Matrix.Basic` import fixed it. Explicit `Nonempty` binders replaced unused
section variables that Lean would discard. Final checks supply the evidence, not earlier
failed attempts.

The fresh scoped sweep checks 55 modules; four rechecks cover the subsequent predicate
renames. There are zero errors, 14 new admission warnings and 17 inherited warnings.
Final style runs cover all ten mathematical modules. The axiom probe covers all 61
source declarations and inventories generated constants. The whole-library root was
not elaborated.

Tracked package sources were exported at manifest pins into the own checkout. Selected
official dependency archives were source-hashed, SHA-256 recorded, copied to the own cache
and extracted serially into the own package tree. The evidence preserves provenance.
Other checkouts' packages and scratch objects were not modified or borrowed as build objects.

## Open work

The external audit must assess source fidelity, representation completeness, sample-count
quantification, machine adaptation, sketches and all skeleton-time readers/instances.
PDFs have not been byte-archived or ingested: this remains an explicit source-fidelity
limitation. No external verdict or gate closure is claimed.

Later phases must supply efficient samplers, arithmetic/loop contracts, valid profiles,
reductions and existing-API bridges. The plan records odd-modulus decoding ties, actual
PRG seed accounting/reindexing and the PW strong-signature size cycle. These are future
obligations, not completed theorems.

**Not yet clear to merge — external review and source archival remain open; the 14
representation statements await their statement gate before proof fills.**
