<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.length_hlDWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Iterated Output Word

**Claim.** For each bit string $x$, the constructed word $W(x)$ has length $4^{\lfloor\log_4 |u|\rfloor}$, where $u$ is the output of the specified one-pass transducer on $x$.

**Proof.** Let $u$ be the one-pass transducer output, and put $t=|u|$. The iteration result for the fourfold-growth step says that iterating this step $t$ times from the encoded state with first component $u$ yields an encoding whose second component has length $4^{\min(t,\operatorname{Nat.log}(4,t))}$ (\texttt{Randomized.iterate\_pow4Step}). The loop-on-encoded-pairs identity identifies the program's loop with precisely this iteration, while the decoding rule for the second component of an encoded pair recovers the indicated word (\texttt{Complexity.BinArith.forLoop\_pairEncode}, \texttt{Complexity.pairSndD\_pairEncode}). Applying these identities to the nested encodings in the definition of $W(x)$ reduces its length to that second-component length. Finally, $\operatorname{Nat.log}(4,t)\le t$, so the minimum is $\operatorname{Nat.log}(4,t)$, giving $4^{\operatorname{Nat.log}(4,t)}$, which is the asserted expression.

**Key facts.** `Randomized.iterate_pow4Step`, `Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairSndD_pairEncode`.
