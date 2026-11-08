<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Switching Failure Indicator

**Claim.** For a Boolean function, threshold $k$, and coordinate restriction, the coordinate-switching failure indicator is nonnegative.

**Proof.** The indicator is defined by a two-case condition: it is $1$ if the decision-tree depth of the restricted function is at least $k$, and $0$ otherwise. Both possible values are nonnegative.
