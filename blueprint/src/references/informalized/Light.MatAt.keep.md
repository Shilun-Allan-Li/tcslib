<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.MatAt.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving a Matrix on an Interval

**Claim.** If μ encodes A at the specified indices and μ' agrees with μ throughout the interval from a to a+nk, then μ' encodes the same matrix entries there.

**Proof.** The interval-agreement hypothesis states that for every b with a≤b<a+nk, μ'(b)=μ(b). This is precisely the pointwise agreement required by `Light.MatAt.congr`, which transfers the matrix-encoding property from μ to μ'.

**Key facts.** `Light.MatAt.congr`.
