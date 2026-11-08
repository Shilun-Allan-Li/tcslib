<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.PMFHasFullSupport.toReal_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Mass Under Full Support

**Claim.** If a probability mass function assigns nonzero mass to every element, then its real-valued mass at each element is strictly positive.

**Proof.** Fix an element $x$. Full support says that the mass $\pi(x)$ is nonzero, and the probability mass function property ensures that this mass is not infinite. The standard positivity criterion for the real value of an extended nonnegative real therefore gives $0<(\pi(x)).toReal$.
