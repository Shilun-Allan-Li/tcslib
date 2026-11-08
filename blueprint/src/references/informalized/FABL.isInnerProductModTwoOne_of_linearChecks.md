<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isInnerProductModTwoOne_of_linearChecks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Checks Certify the Inner Product

**Claim.** If all the stated linear checks hold for the proof string, then the modulo-two inner product of the two blocks of the Boolean input string is $1$.

**Proof.** The checks determine every prefix bit, interpreted in $\mathbb F_2$, from the input string: at each position $k$, the prefix value equals the corresponding accumulated inner-product prefix (\(\texttt{FABL.innerProductPrefixProof\_eq\_of\_checks}\)). In particular, this holds at the final position $m$. The final-position check requires the last proof bit to be true; under the Boolean-to-$\mathbb F_2$ encoding, true is $1$ (\(\texttt{FABL.pcppBoolF\u2082Equiv\_true}\)). Thus the final accumulated prefix value is $1$. The full prefix value agrees with the inner product of the two input blocks (\(\texttt{FABL.innerProductPrefixBit\_full}\)), so that inner product is $1$.

**Key facts.** `FABL.innerProductPrefixProof_eq_of_checks`, `FABL.pcppBoolF₂Equiv_true`, `FABL.innerProductPrefixBit_full`.
