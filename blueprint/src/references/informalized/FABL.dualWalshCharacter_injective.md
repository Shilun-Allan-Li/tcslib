<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualWalshCharacter_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of dual Walsh characters

**Claim.** The map sending a linear functional on a vector space over $\mathbb{F}_2$ to its dual Walsh character is injective.

**Proof.** Suppose two linear functionals give the same Walsh character. Evaluating that equality at any vector $x$ shows that their binary signs agree at their respective values on $x$. The binary sign map is injective (`FABL.binarySign_injective`), so the functionals agree at every $x$. Extensionality of linear maps then gives equality of the functionals, proving injectivity.

**Key facts.** `FABL.binarySign_injective`.
