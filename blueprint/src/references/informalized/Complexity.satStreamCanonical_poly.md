<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamCanonical_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time of the Canonicalizer

**Claim.** The canonicalizer that returns its input when the complete syntax scan accepts it and returns the one-bit word $0$ otherwise is computable in polynomial time.

**Proof.** The syntax test, which returns the one-bit word recording whether the input passes the complete scan, is polynomial-time computable ($\texttt{satSyntax_poly}$). The identity function is polynomial-time computable ($\texttt{polyTimeComputable_id}$), and the constant function returning $[\text{false}]$ is polynomial-time computable ($\texttt{sat_pt_const}$). Polynomial-time computation is closed under choosing between two polynomial-time outputs according to a polynomial-time Boolean test ($\texttt{sat_pt_cond}$). Applying this closure to the syntax test, the identity output on acceptance, and the constant one-bit output on rejection gives the canonicalizer.

**Key facts.** `Complexity.satSyntax_poly`, `Complexity.polyTimeComputable_id`, `Complexity.sat_pt_const`, `Complexity.sat_pt_cond`.
