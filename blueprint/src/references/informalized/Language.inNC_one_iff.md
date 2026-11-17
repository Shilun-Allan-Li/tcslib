<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.inNC_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-One Circuit Characterizations

**Claim.** For every Boolean language, recognition by polynomial-size Boolean circuit trees with fan-in at most two and depth at most $b(\log_2 n+1)$ for some $b$ is equivalent to recognition by polynomial-size DAG circuits with fan-in at most two and the same depth form.

**Proof.** The forward direction is the depth-one conversion from the DAG class to the tree class (`Language.InNC.inTreeNC_one`). The reverse direction follows from the general inclusion of the tree class in the DAG class, which preserves the depth parameter (`Language.InTreeNC.inNC`). Taking the parameter to be one yields both implications.

**Key facts.** `Language.InNC.inTreeNC_one`, `Language.InTreeNC.inNC`.
