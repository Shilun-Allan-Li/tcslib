<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.pairEncode_pairEncode_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Nested Pair Encoding

**Claim.** The encoding of $(u,\langle\alpha,x\rangle)$ has length $2|u|+2|\alpha|+4+|x|$.

**Proof.** The length formula for a pair encoding says that encoding a first component $v$ with a tail $z$ has length $2|v|+2+|z|$. Apply it to the outer encoding, then apply it again to the inner encoding of $(\alpha,x)$. The result is $2|u|+2+(2|\alpha|+2+|x|)$, which rearranges to the claimed expression.

**Key facts.** `Turing.universal_pair_length`.
