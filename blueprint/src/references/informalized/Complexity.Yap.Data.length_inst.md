<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.length_inst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Nested Pair Encoding

**Claim.** Under the stated polynomial length conditions on $u$ and $v$, the length of the nested encoding $x,u,v$ equals the given expression.

**Proof.** The pair encoding of strings $a,b$ has length $2|a|+2+|b|$ (`Turing.length_pairEncode`). Apply this first to the inner pair: its length is $2|x|+2+|u|$. Apply it again to the outer pair to obtain twice that inner length, plus $2+|v|$. Substitute $|u|=C_1(|x|+1)^{c_1}$ and $|v|=C_2(|x,u|+1)^{c_2}$; the resulting expression is exactly the asserted formula.

**Key facts.** `Turing.length_pairEncode`.
