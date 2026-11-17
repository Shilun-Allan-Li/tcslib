<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.length_executableSmallBiasGeneratorList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Bias Generator List Length

**Claim.** For any natural number $n$ and positive natural number $\ell$, a certified binary field implementation of degree $\ell$ has an executable small-bias generator list of length $2^{2\ell}$.

**Proof.** The generator list is obtained by mapping a function over the list of pairs of binary vectors. Mapping preserves list length, so its length is the length of that pair list. The length formula for binary vector pairs gives $2^{2\ell}$ (\texttt{length\_binaryVectorPairs}).

**Key facts.** `FABL.length_binaryVectorPairs`.
