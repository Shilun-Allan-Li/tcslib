<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mean_bribeFunction_majority_eq_of_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority mean depends on coalition size

**Claim.** If coordinate sets $A$ and $B$ have equal cardinality, then bribing either set to the same sign $b$ gives the same mean for majority.

**Proof.** Choose a coordinate permutation transporting $A$ to $B$, as supplied by the equal-cardinality construction used in the proof. Reindex the uniform mean by the induced permutation of inputs; this does not change the mean. The bribery-permutation identity ($\texttt{FABL.bribeInput_permuteInput_coalitionTransport}$) says that bribing $B$ and then permuting the input agrees with permuting the input first and bribing $A$. The permutation cancellation in the proof aligns these inputs. Majority is invariant under coordinate permutations ($\texttt{FABL.majority_symmetric}$), so the two bribed majority values agree at corresponding inputs. Their means are therefore equal.

**Key facts.** `FABL.bribeInput_permuteInput_coalitionTransport`, `FABL.majority_symmetric`.
