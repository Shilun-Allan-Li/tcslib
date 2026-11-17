<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.nonzero_iff_restrictBits_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Codes and Restricted Bits

**Claim.** A width-$w$ switching block code has a position in its position set with bit $1$ if and only if its bit assignment restricted to that set is not the zero function.

**Proof.** If some designated position has bit $1$, the restriction takes value $1$ there, so it cannot be the zero function. Conversely, suppose there is no designated position with bit $1$. At every position in the set the bit must then be $0$, since the two-element field has only the values $0$ and $1$. Thus the restricted assignment is the zero function. Taking the contrapositive, a nonzero restriction implies that some designated position has bit $1$.
