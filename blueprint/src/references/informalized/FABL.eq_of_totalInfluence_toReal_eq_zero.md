<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.eq_of_totalInfluence_toReal_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero total influence implies constancy

**Claim.** If a Boolean function on the sign cube has zero total influence, then it takes the same value at every pair of inputs and is therefore constant.

**Proof.** Apply the Fourier expansion at arbitrary inputs x and y. The terms indexed by the empty set agree, since the empty monomial is 1. Every nonempty set S has zero Fourier coefficient when total influence is zero (`FABL.fourierCoeff_eq_zero_of_totalInfluence_eq_zero`), so all remaining terms vanish. The two real-valued Fourier expansions are consequently equal. Injectivity of `signValue` (`FABL.signValue_injective`) converts this equality of real values back to f(x)=f(y). Since x and y were arbitrary, f is constant.

**Key facts.** `FABL.fourier_expansion`, `FABL.fourierCoeff_eq_zero_of_totalInfluence_eq_zero`, `FABL.signValue_injective`.
