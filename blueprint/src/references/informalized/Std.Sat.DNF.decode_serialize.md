<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.DNF.decode_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverting DNF serialization

**Claim.** For every DNF formula $\psi$ over variables indexed by $\mathbb{N}$, decoding its binary serialization returns $\psi$.

**Proof.** DNF serialization applies the CNF serializer to the list of terms, and DNF decoding wraps the CNF decoder's result back as a DNF formula. The CNF decoding theorem says that decoding the serialization of any such list recovers that list ($\mathrm{decode\_serialize}$). Applying it to the terms of $\psi$ therefore recovers $\psi$.

**Key facts.** `Std.Sat.CNF.decode_serialize`.
