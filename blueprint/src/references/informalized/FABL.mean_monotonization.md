<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_monotonization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Preservation Under Monotonization

**Claim.** For a Boolean function on the sign cube, monotonizing it preserves its uniform mean after its values are viewed as real numbers.

**Proof.** The monotonization applies coordinate polarizations along the list of all coordinates. The mean-preservation theorem for a list of coordinate polarizations (\(\texttt{FABL.mean_polarizeCoordinates}\)) says that this entire sequence leaves the mean unchanged. Applying it to the list of all coordinates gives the claimed equality.

**Key facts.** `FABL.mean_polarizeCoordinates`.
