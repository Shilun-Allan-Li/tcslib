<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.fourierCoeff_oddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of the odd part

**Claim.** For a real-valued function $f$ on the $n$-dimensional sign cube and a coordinate set $S$, the Fourier coefficient of $x\mapsto(f(x)-f(-x))/2$ at $S$ is $(1-(-1)^{|S|})\widehat f(S)/2$.

**Proof.** By the definition of the odd part, its coefficient is the expectation of $(f(x)-f(-x))$ times the character at $S$, divided by $2$. Linearity of expectation separates this into the coefficient of $f$ and the expectation of $f(-x)$ against that character. The latter is the coefficient of the function $x\mapsto f(-x)$ at $S$. Negating the input multiplies a degree-$|S|$ character by $(-1)^{|S|}$, so the coefficient is $(-1)^{|S|}\widehat f(S)$ (the negation identity `fourierCoeff_comp_neg`). Subtracting and dividing by $2$ gives the claimed formula.

**Key facts.** `FABL.fourierCoeff_comp_neg`.
