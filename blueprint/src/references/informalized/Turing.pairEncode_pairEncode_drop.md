<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.pairEncode_pairEncode_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail of a Nested Pair Encoding

**Claim.** Removing the first $2|u|+2|\alpha|+4$ bits from the encoding of $(u,\langle\alpha,x\rangle)$ leaves exactly $x$.

**Proof.** First, for any bit strings $v,z$, the prefix preceding $z$ in their pair encoding has length $2|v|+2$: each bit of $v$ is repeated twice, followed by the two-bit delimiter. Thus dropping that many bits from the encoding of $(v,z)$ leaves $z$. Apply this fact first to the outer encoding with $v=u$ and $z=\langle\alpha,x\rangle$, then to the inner encoding with $v=\alpha$ and $z=x$. Dropping the combined number of bits is the same as performing these two drops in succession, and the total is $(2|u|+2)+(2|\alpha|+2)=2|u|+2|\alpha|+4$.

**Key facts.** `Turing.universal_pair_length`.
