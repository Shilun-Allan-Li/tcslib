# Levin padding checkpoint

Base `19b92fe1c1f5b86aa9a5e27e3b011b0fa5e69460`, with Lean 4.25.0 and the pinned Mathlib.
The isolated source proves the complete linear-time word formula of
`PadQuad.exists_linearTime_gStr`. The conditional assembly and the
unconditional root construction check in the same olean tree. Lean reports
`propext`, `Classical.choice`, and `Quot.sound` as their axioms.

- The fixed-degree binary root uses interval halving with an invariant bounded by
  the input's binary width. The length scan is linear, and a polynomial in the
  binary width fits a linear budget in the original length.
- At degree one, a transducer emits one token per input bit after the first.
  At higher degrees, the existing emitting loop takes binary fuel and emits one
  token per positive decrement. On the canonical shifted-root word its time is
  bounded by the square of the root plus one, up to a fixed factor.
- The unary length polynomial uses the sharp monomial emitter and timed
  concatenation. The paired call charges the original evaluator at the actual
  payload length. The suffix and zero padding are carried through that call,
  and the final split cuts the output to twice the input length.

The declaration dependency trace reaches 1884 local declarations.
Its intersection with the #248 cleanup ledger contains 52 historical
diagnostics across 35 declarations. The matching IDs and paths are in
`LevinDependencyScreen.json`. The earlier reuse ruling was for the
Claude efficiency fill. The Levin candidate needs a decision on using these
providers while the inherited seal repairs are deferred.

Seyoon selected Codex for the Levin audit, with the findings returned in chat.
Resume by integrating the checked formula at the frozen `exists_linearTime_gStr`
header, checking the combined source and its seals, and pinning the audit once
the dependency disposition is settled. The canonizer's time bound is a separate
proof obligation.

[Checked Lean source, provider diffs, logs, replay order and SHA-256 manifest](levin-padding-checkpoint.zip)

Archive SHA-256 `53b73255f0bc314f62c6420d05bd03b2a50ff0e3b4e251e484d765c0bf3da667`

**Not yet clear to merge — the checked proof needs source integration, a dependency disposition, and audit.**
