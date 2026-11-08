<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_pair_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsed pairs reconstruct their encoding

**Claim.** Whenever the aligned pair parser succeeds on $z$, encoding its decoded first and second components recovers $z$.

**Proof.** Consider the value of the parser on $z$. It cannot be `none`, since that would contradict the hypothesis that parsing succeeds. Thus it is some pair $(a,b)$. The decoded-component functions therefore return $a$ and $b$, respectively. The reconstruction theorem for a successful parse says that a word decoded as $(a,b)$ is exactly the pair encoding of $(a,b)$ (`Turing.eq_pairEncode_of_pairDecode`). Substituting the decoded components gives the claim.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`.
