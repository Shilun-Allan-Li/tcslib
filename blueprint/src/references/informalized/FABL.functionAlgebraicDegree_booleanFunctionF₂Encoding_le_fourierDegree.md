<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierDegreeBridge.lean :: FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic degree and Fourier degree

**Claim.** For a Boolean function on the sign cube, the algebraic degree of its $\{-1,1\}\to\mathbb{F}_2$ encoding is at most the Fourier degree of the original function.

**Proof.** The proof applies the previously established polynomial comparison theorem directly: for every Boolean function, the algebraic degree of its $\{-1,1\}\to\mathbb{F}_2$ encoding is at most the Fourier degree of its real-valued version (`FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree_viaPolynomial`). This is precisely the stated bound.

**Key facts.** `FABL.functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree_viaPolynomial`.
