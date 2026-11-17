<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.improvedFKNBalancedLift_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-valued balanced lift under a swap

**Claim.** The real-valued version of the balanced lift obtained by swapping the new first coordinate with coordinate $i+1$ equals the real-valued balanced lift composed with that coordinate swap.

**Proof.** Both sides evaluate an input by first swapping the indicated coordinates and then applying the balanced lift, followed by passage from its sign-valued output to its real value. Thus they agree pointwise, and hence are the same function.
