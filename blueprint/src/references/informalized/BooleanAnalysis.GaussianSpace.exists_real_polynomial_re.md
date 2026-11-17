<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Polynomial.lean :: BooleanAnalysis.GaussianSpace.exists_real_polynomial_re -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial representation of a real part

**Claim.** For any complex polynomial in $n$ variables, there is a real polynomial whose value at every real input is the real part of the complex polynomial's value there.

**Proof.** Induct on the construction of the complex polynomial. For a constant $c$, use the real constant $\operatorname{Re}(c)$. If polynomials $P$ and $R$ have real-polynomial representatives $P'$ and $R'$, then $P'+R'$ represents the real part of $P+R$, since real parts add. In the remaining induction step, multiply a polynomial $P$ by a variable $X_i$. If $P'$ represents its real part on real inputs, then $P'X_i$ represents the real part of $PX_i$: at a real input, the evaluated variable is real, so $\operatorname{Re}(P(x)x_i)=\operatorname{Re}(P(x))x_i$. These cases cover the polynomial induction and produce the required real polynomial.
