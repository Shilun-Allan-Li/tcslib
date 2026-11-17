<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.relativeHammingDist_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Relative Hamming Distance

**Claim.** For any two Boolean functions on the sign cube of dimension $n$, their relative Hamming distance is symmetric in the two functions.

**Proof.** By definition, relative Hamming distance is the Hamming distance divided by the size of the domain. Hamming distance counts inputs where the function values differ, a condition unchanged when the two functions are interchanged. The denominators are therefore identical, giving the claimed equality.
