<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_primrec_parity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Rank Parity

**Claim.** For a bit string $s$, the function returning the singleton list containing whether $r(s)$ is odd is primitive recursive.

**Proof.** The rank function $s\mapsto r(s)$ is primitive recursive (\texttt{Complexity.ntc\_primrec\_rank}). The parity predicate on natural numbers is primitive recursive, so composing it with the rank gives the Boolean value indicating whether $r(s)$ is odd. Consing that value onto the constant empty list gives the required singleton list.

**Key facts.** `Complexity.ntc_primrec_rank`.
