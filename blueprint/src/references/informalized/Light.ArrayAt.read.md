<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ArrayAt.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an Array Entry

**Claim.** For an array satisfying the stated conditions, each index $i<N$ reads the value $\mu(a+i)$ from the list, with out-of-range access interpreted by the default value $0$.

**Proof.** The array conditions give the corresponding list-at property: the list has length $N$ and its entries agree with the specified values of $\mu$ up to that length. The list-at reading result therefore says that whenever $i<N$, $\mu(a+i)=l.getD(i,0)$, as required.

**Key facts.** `Light.ArrayAt.listAt`, `Light.ListAt.read`.
