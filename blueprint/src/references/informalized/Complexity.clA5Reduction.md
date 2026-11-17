<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Reduces to SAT

**Claim.** Every language over the Boolean alphabet in NP has a polynomial-time many-one reduction to SAT.

**Proof.** Extract from NP membership a verifier machine, a polynomially bounded certificate length, and the equivalence between membership and existence of an accepted certificate (`Complexity.clNPVerifier`). Map an input to the serialized tableau formula for that verifier, using the producer horizon specified in the construction. This map is polynomial-time computable (`Complexity.clA5OutputIdentity`). The tableau equivalence (`Complexity.clA5Equisat`) says that its formula is satisfiable exactly when there is a certificate of the prescribed length accepted by the verifier. The NP characterization makes this equivalent to membership in the original language. Finally, serialization followed by decoding returns the same formula (`Std.Sat.CNF.decode_serialize`), so the output is satisfiable exactly on inputs in the language.

**Key facts.** `Complexity.clNPVerifier`, `Complexity.clA5OutputIdentity`, `Complexity.clA5Equisat`, `Std.Sat.CNF.decode_serialize`.
