<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.monomial_tailFrequency_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial Under Coordinate Shift

**Claim.** Shifting the coordinates of $S$ forward by one and evaluating the resulting monomial on the vector formed by placing $b$ before $x$ gives the same value as the monomial indexed by $S$ at $x$.

**Proof.** The map sending each coordinate $i$ to its successor identifies the shifted set with $S$ without changing its elements' order or multiplicities. At each such successor coordinate, the vector formed by placing $b$ before $x$ has value $x_i$. Thus the product defining the shifted monomial has exactly the same factors as the product defining the original monomial, so the two products agree.
