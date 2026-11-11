# Independent Levin proof prerequisites

Base `37e161131e68ff347ed59b59b9ebcd66ffa9ea43`. The arithmetic probe was
also checked in the separate Gate 09 source tree. The Levin source
is unchanged there.

- **`PadQuad.exists_linearTime_gStr`.** The checked image bound handles
  every input length, including the finite range below the dominance
  threshold. It bounds the output unary length plus the original
  machine's call cost by `B * (|z| + 1)`. The proof uses
  `PadQuad.nu_pow_le`, `NUPPT.length_advInput` and monotonicity of
  the length polynomial. The complete word formula now checks in an
  isolated tree, including the linear-time shifted unary root and the
  output-sensitive unary polynomial evaluator. See the
  [Levin padding checkpoint](levin-padding-checkpoint.md) for the checked
  proof and its dependency screen.
- **`exists_canonizerExp`.** The existing `EffectiveMachineCode` witness
  has a canonizer bound obtained by a finite maximum of halting
  times. The concrete decoder and padded round-trip theorem are
  available. To meet `CanonizerExp` the machine needs a quantitative
  bound for every input, including malformed codes. The bounded
  parse-and-reserialize route should check the minimum table length
  before iterating over a declared state count.

[Checked image-bound probe and diagnostics](levin-probe.zip)

**Not yet clear to merge — the padding proof awaits integration and audit, and the canonizer bound remains open.**
