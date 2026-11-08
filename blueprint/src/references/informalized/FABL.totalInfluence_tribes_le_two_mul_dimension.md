<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.totalInfluence_tribes_le_two_mul_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear tribes influence bound

**Claim.** The total influence of tribes on $s$ blocks of $w$ signs is at most twice its number of input coordinates, $2sw$.

**Proof.** The tribes function has DNF width at most its full dimension, namely $sw$ (\texttt{hasDNFWidthLE\_dimension}). The influence bound for a Boolean function whose DNF width is at most $w$ states that its total influence is at most twice that width (\texttt{totalInfluence\_le\_two\_mul\_of\_hasDNFWidthLE}). Applying that result with width $sw$ yields the bound $2sw$.

**Key facts.** `FABL.hasDNFWidthLE_dimension`, `FABL.totalInfluence_le_two_mul_of_hasDNFWidthLE`.
