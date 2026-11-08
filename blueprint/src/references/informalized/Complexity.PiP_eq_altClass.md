<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.PiP_eq_altClass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Alternation Characterization

**Claim.** For every natural number $i$, the class of languages whose complements belong to $\Sigma_i^P$ equals the class characterized by $i$ alternating quantifier blocks beginning universally, with polynomially bounded witnesses and a polynomial-time predicate.

**Proof.** To prove equality of the two classes, extensionality reduces the claim to showing, for each language $L$, that membership in $\Pi_i^P$ is equivalent to the stated universal-starting alternating characterization. The membership characterization lemma for $\Pi_i^P$ gives exactly this equivalence, with a polynomial verifier and the prescribed witness bound. Thus the two sets have the same members.

**Key facts.** `Complexity.mem_PiP_iff`.
