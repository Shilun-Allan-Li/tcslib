<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.wd_toInt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed word encoding

**Claim.** For every word width $W$ and every $W$-bit vector $w$, encoding the signed integer represented by $w$ recovers $w$.

**Proof.** By the defining property of signed conversion for bit vectors, applying the width-$W$ integer encoding to the signed value of $w$ returns the original bit vector. This is exactly the identity `BitVec.ofInt_toInt`.
