<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.f₂CoordinateVector_ne_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct coordinate vectors

**Claim.** Standard coordinate vectors indexed by distinct indices are distinct.

**Proof.** Suppose the vectors indexed by $i$ and $j$ were equal. Evaluating their coordinates at $i$ would give equal values. The vector indexed by $i$ has value $1$ there, while the vector indexed by $j$ has value $0$ because $i\ne j$. This contradiction proves the vectors are distinct.
