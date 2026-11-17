<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.wrote_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing on an empty interval

**Claim.** Writing values of $f$ on the empty interval $dst\le a<dst$ leaves $\mu$ unchanged.

**Proof.** At any index $a$, the conditions $dst\le a$ and $a<dst+0=dst$ cannot both hold. The write rule therefore selects $\mu(a)$ at every index, so the two functions are equal.
