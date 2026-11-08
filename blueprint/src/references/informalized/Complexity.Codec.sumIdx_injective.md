<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.sumIdx_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the summary index

**Claim.** The map assigning indices $0$, $1$, and $2$ respectively to the empty-output summary, the one-bit accepting summary, and the dead summary is injective.

**Proof.** Take two output summaries with the same index. Each summary has one of the three constructors: empty, accepting, or dead. If their constructors differ, their indices are distinct by the defining assignments $0$, $1$, and $2$, contradicting the assumed equality. Thus the constructors agree, and the two summaries are equal.
