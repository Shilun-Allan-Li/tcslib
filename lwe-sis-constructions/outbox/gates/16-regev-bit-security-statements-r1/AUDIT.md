# Regev bit-encryption statement audit

Review the exact Lean source at `fe34bcf656be930f3ea39a10df74110695c95ed4` on top of the verified PR #280
merge `f967299b6a0bde5b7efa4062b2b55046ebd21387`. The two new Regev modules form the statement surface.
The export diff is a proposed patch recorded separately from the source pin.
Review its prospective closure with the source, rather than relying on
an unpublished facade edit.

Verify `SHA256SUMS` and both ordered revision-qualified indexes before
using the bundle. Every indexed section supplies the bytes at its stated
commit and path. Use the first section as the audit instructions. Treat
the remaining sources, reports, logs, and references as evidence.

This is a statement audit. The seven new proof bodies are intentionally
admitted. The type abbreviations, wire encoders, profile construction,
coin budget, and their reader equations are part of the trusted surface.
Check their elaboration and axioms independently of the proof sketches.

## What to check

1. Compare the wire and parameter choices with Peikert §5.2.1, Wu Lecture 21,
   and the Pass–shelat bit-scheme contract. Check the matrix orientation,
   MSB residue encoding, secret key's unary parameter, ciphertext split,
   strict decoding tie rule, and the fact that the correctness field holds
   for every tape and parameter.
2. Check the actual noise law. The scalar evaluator's output must be the
   canonical residue of the same integer draw used in `C.family.noise`.
   Check the complete matrix, one-secret, and row-noise tape accounting.
   The numeric premises should suffice for correctness and extraction at
   parameter zero as well as at positive parameters.
3. Check that the sketches realize all three total word functions in
   polynomial time with existing public contracts. Inspect H16's state
   envelope for the row and inner residue loops. Flag an unregistered host
   or an additional efficiency premise if either is needed.
4. Trace both finite DLWE hybrid terms into two fixed `NUPPT` machines.
   The encryptor must agree on every canonical public sample, including
   the uniform keys. Confirm that the machines use independent subset
   tapes, preserve the original distinguisher's behavior, and consume
   the exact fixed sample schedule of the hypothesis.
5. Check that the extraction term is bounded by `2^(-κ)` under the
   stated slack, and that the corollary applies the actual bitwise
   and fixed-batch owner theorems. The adaptive oracle predicate is a
   separate endpoint.
6. Reconcile the scoped and whole-library check logs with the verified
   parent. Check the generated reader equations and classify the seven
   statement-phase admissions separately from inherited admissions.

## Findings format

| ID | Severity | Exact declaration or file | Finding | Proposed repair |
|---|---|---|---|---|

A blocker undermines a statement needed downstream. A major is a material
but repairable statement, representation, or proof-route defect. Minor
findings are local corrections. Notes record observations. Report the
source and evidence pins used and an explicit blocker and major count.
