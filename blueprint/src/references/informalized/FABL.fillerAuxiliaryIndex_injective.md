<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.fillerAuxiliaryIndex_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Auxiliary Indices

**Claim.** For $a+3\le K$, the map sending $j\in\{0,1,2\}$ to the coordinate in the block of $K$ indices, offset by $r$, whose within-block index is $a+j$, is injective.

**Proof.** Suppose two inputs have the same image. The map that places an index into the block of size $K$ after the first $r$ coordinates is injective (`Fin.natAdd_injective`), so the within-block indices agree. Applying this equality to their natural-number values gives $a+\mathrm{first}=a+\mathrm{second}$. Cancellation of the common summand $a$ shows the inputs have equal values, hence are equal as elements of the finite index type.
