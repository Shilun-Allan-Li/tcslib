<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.size_parityDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity DNF size

**Claim.** For positive $n$, the DNF with one minterm for each input where parity on $n$ coordinates equals $-1$ has exactly $2^{n-1}$ terms.

**Proof.** The parity DNF is defined to be the minterm DNF of parity on all coordinates. The result that this minterm DNF has size $2^{n-1}$ (\(`size_mintermDNF_parityFunction_univ`\)) therefore gives the asserted term count directly.

**Key facts.** `FABL.size_mintermDNF_parityFunction_univ`.
