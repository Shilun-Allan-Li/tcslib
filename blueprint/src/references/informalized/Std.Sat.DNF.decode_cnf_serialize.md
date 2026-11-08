<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/DNF.lean :: Std.Sat.DNF.decode_cnf_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a serialized DNF formula

**Claim.** For every DNF formula $\psi$ over variables indexed by $\mathbb{N}$, decoding the binary serialization of $\psi$ returns $\psi$.

**Proof.** A DNF formula is represented by its list of terms, which is a CNF formula as far as the serialization routines are concerned. The CNF decoding theorem states that decoding the serialization of this list returns the same list ($\mathrm{decode\_serialize}$). DNF decoding simply wraps the decoded list as a DNF formula, so the result is $\psi$.

**Key facts.** `Std.Sat.CNF.decode_serialize`.
