<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformSign_pTwoHypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Bit Hypercontractivity

**Claim.** For a uniform sign and $1\le p\le2$, the affine random variable with noise parameter $\sqrt{p-1}$ has its $L^2$ norm bounded by the $L^p$ norm of the corresponding unnoised affine random variable.

**Proof.** Fix real numbers $a,b$. By the identification of the extended-real-indexed uniform norm with the ordinary norm at a finite exponent ($\texttt{uniformLpNormENNReal_coe}$), the required inequality reduces to the one-bit affine estimate. That estimate, which applies whenever $1\le p\le2$, gives exactly the desired comparison for $a+\sqrt{p-1}\,bX$ and $a+bX$ ($\texttt{oneBit_pTwo_sharp}$).

**Key facts.** `FABL.uniformLpNormENNReal_coe`, `FABL.oneBit_pTwo_sharp`.
