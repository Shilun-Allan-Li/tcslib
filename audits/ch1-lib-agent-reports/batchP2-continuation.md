# P2 continuation frontier

Status: targets 12 and 13 filled; 14 and 15 retain their original admitted bodies.
Required original base: 90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee.
This checkpoint: f4167fc821188ef5c8ae65d340f477a3e794aa95.
Only Primitives.lean is changed. Follow the next maintainer brief for its exact
integrated base; this document does not authorize work on a different branch.

## Target 14: pairMapSnd

Available and proved in this checkpoint:

- `catalogPair_inverse`: a successful parse reconstructs its exact encoding.
- `catalogPayload_length`: the total suffix extractor's output length is at most
  the physical input length, including the malformed empty default.
- `catalogPayload_computes`: the explicit machine
  `bufferedCompTM (pairExtractTM false true) Mg` computes
  `g ((pairDecode x).map Prod.snd |>.getD [])` within
  `6 * (n + 1) + Tg n + 1`, using the actual suffix-length bound.
- `catalogRewind`: quantitative input rewind preserving all tapes/output.
- `lenStart`: a concrete `capture_run` host-instantiation example, choosing the
  least halt time to satisfy its liveness guard. It is specialized to
  `pairCountTM`, so adapt its proof to the threaded-map host instead of pretending
  its endpoint already supplies that host.

Still missing: the finite controller retaining/replaying the first component
and capturing/replaying the transformed payload, with malformed-input silence.
`catalogPayload_computes` by itself emits only the transformed payload, so it is
not the threaded map. One possible continuation is to capture this proved total
payload machine on the original input, silently validate/recover the encoded
first-component prefix, and replay prefix/separator plus captured output. Prove
the exact phase seams and total bound; the sketch alone discharges nothing.
The direct parser-plus-relocated-capture route in the brief is also available.

Do not use a coarse composition bound `Tg (5*(n+1))` and then assert it is a
constant multiple of `Tg n`: arbitrary monotonicity does not imply that. Use the
proved actual-payload bound. `capture_run` is proved and must introduce no
admission. Nothing in target 14 is sanctioned to depend on `sorryAx`.

## Target 15: splitSolve

No target-15 body or instance proof is delivered. The original audited
`exists_loopFindTM` route is still binding. Instantiate the specified unary
candidate state, append-or-stall step, length invariant, acceptance equation,
encoded split payload, and fuel `R n = n`. Use the existing lengthBits witness
for fuel. Construct and prove startup, each candidate round, scratch restoration,
anchor discipline, and a positive-time stall beyond the final candidate.

The invariant admits arbitrary bit patterns unless explicitly strengthened and
proved; a round that uses lengths must preserve existing bits when appending or
stalling. Prove the `Nat.beq_eq`/range-search and unary-orbit bridge, then the
final exponent-`e+2` arithmetic. The only allowed root is `loopHost_contracts`,
reached through `exists_loopFindTM`, until the concurrent loop fill is integrated.
This checkpoint does not use that root.

## Reproduction

Run the pinned Lean 4.25.0 per-module checker in the committed 57-module order.
Never run `lake build`. Use a fresh olean directory and run
`verification/PrimitiveAxioms.lean` with that directory first on `LEAN_PATH`.
The expected current roots are empty for the first 13 targets and the 29 new
private declarations, and exactly each pending theorem itself for targets 14–15.
Update those expectations when the actual target proofs are completed.

The source's public docstrings and signatures are preserved. Append implementation
notes when adapting routes; do not alter the audited statements. Every helper
stays private and is listed in the next report.

Notation: `n` is input length; `Tg` is the given monotone running-time function;
`R` is loop fuel; `e` is the target's polynomial exponent.
