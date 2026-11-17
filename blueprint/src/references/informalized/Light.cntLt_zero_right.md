<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_zero_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count over an empty range

**Claim.** For any function $kf:\mathbb{N}\to\mathbb{N}$ and $t\in\mathbb{N}$, the number of indices $i<0$ satisfying $kf(i)<t$ is zero.

**Proof.** By definition, this count is the count of a predicate over a range of length zero. The empty range has no indices, so its count is $0$.
