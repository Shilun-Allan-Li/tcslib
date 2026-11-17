<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.inputProofWord_restrictOuterProof_liftOuterAddress -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction at lifted addresses

**Claim.** Evaluating the extended word at a lifted address agrees with evaluating the word formed from the input and the restriction of the extended proof at the original address.

**Proof.** Split on whether the address is an input or proof address. An input address is unchanged by lifting, so both sides give the same entry of the input word. At a proof address $j$, lifting sends it to the extended proof position corresponding to $j$ among the first $\ell$ positions; restricting the extended proof reads precisely that position. Hence the two evaluations agree.
