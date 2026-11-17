<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeComplexTerm_re -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Part of a Mod-Three Complex Term

**Claim.** The real part of the specified complex term is $(-1)^{(|S|\bmod 4)/2}(\sqrt{3})^{|S|}\prod_{i\in S}x_i$ when $|S|$ is even, and is $0$ when $|S|$ is odd.

**Proof.** Split according to whether $|S|$ is even. In the even case, the real part of the product of the real scalar $(-\sqrt{3})^{|S|}\mathrm{monomial}(S,x)$ and $\mathrm{i}^{|S|}$ is that scalar times the real part of $\mathrm{i}^{|S|}$. The even-power phase formula gives $\operatorname{Re}(\mathrm{i}^{|S|})=(-1)^{(|S|\bmod 4)/2}$ (`re_I_pow_eq_modFourPhase`). Since the exponent is even, $(-\sqrt{3})^{|S|}=(\sqrt{3})^{|S|}$, yielding the stated expression. In the odd case, the real part of $\mathrm{i}^{|S|}$ vanishes (`re_I_pow_eq_zero_of_odd`), so the whole real part is zero.

**Key facts.** `FABL.re_I_pow_eq_modFourPhase`, `FABL.re_I_pow_eq_zero_of_odd`.
