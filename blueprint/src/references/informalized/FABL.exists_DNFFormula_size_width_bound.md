<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.exists_DNFFormula_size_width_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded DNF Representation

**Claim.** Every Boolean function on $\{−1,1\}^n$ has a DNF representation with at most $2^n$ terms and width at most $n$.

**Proof.** Use the minterm DNF associated with the function. Its size is at most $2^n$ (`size_mintermDNF_le`), its width is at most $n$ (`width_mintermDNF_le`), and it represents the original function (`mintermDNF_toBooleanFunction`). These three properties give the required representation and bounds.

**Key facts.** `FABL.size_mintermDNF_le`, `FABL.width_mintermDNF_le`, `FABL.mintermDNF_toBooleanFunction`.
