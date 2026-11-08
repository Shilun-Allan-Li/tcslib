<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.matrixRowSpan_eq_span_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Span as a Generated Subspace

**Claim.** The image of left multiplication by an $m\times n$ matrix $H$ over $\mathbb{F}_2$ is the subspace spanned by the rows of $H$.

**Proof.** By the matrix row-span identity (`range_vecMulLinear`), the range of the linear map given by left multiplication by $H$ is exactly the span of the vectors obtained as rows of $H$. Since `matrixRowSpan H` is defined to be that range, the claimed equality follows.
