<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceVerifier_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier Membership for a Fixed Split

**Claim.** When $|u|=C(|x|+1)^c$, the concatenation $xu$ belongs to the verifier language exactly when the run on $x$ under $u$ halts with output $[1]$.

**Proof.** For membership, the verifier supplies a split $y,v$ of the concatenated word, with certificate length prescribed by $C,c$. The given split $x,u$ has that same prescribed length. The strict increase of the total encoded length $n+C(n+1)^c$ (`Turing.certificateLength_strictMono`) and uniqueness of fixed-length append splits (`Turing.append_split_unique`) force $y=x$ and $v=u$. The verifier's halting and output conditions are therefore precisely the asserted conditions. Conversely, if the run under $u$ halts with output $[1]$, choose $x,u$ themselves as the verifier's split; the length hypothesis and concatenation equality provide the remaining membership witnesses.

**Key facts.** `Turing.certificateLength_strictMono`, `Turing.append_split_unique`.
