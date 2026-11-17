<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.pairedVerifier_malformed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Malformed pairs are rejected

**Claim.** If the aligned pair parser is undefined on a finite bit string $y$, then $y$ does not belong to the paired verifier language defined by $C$, $c$, and $V$.

**Proof.** Membership would provide strings $x$ and $u$ such that parsing $y$ returns `some (x,u)`, along with the length and language conditions. But the hypothesis says parsing returns `none`. These two parser results are incompatible, so such witnesses cannot exist.
