<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.isKJunta_zero_of_totalInfluence_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero influence gives a constant

**Claim.** If the real sign representation of a Boolean function has total influence zero, then the function depends on at most zero coordinates.

**Proof.** Choose the empty set as the proposed set of relevant coordinates; it has cardinality zero. To check dependence on this set, take any two inputs. The zero-total-influence result \texttt{eq\_of\_totalInfluence\_toReal\_eq\_zero} says that their function values are equal. Thus the function is constant and depends on no coordinates.

**Key facts.** `FABL.eq_of_totalInfluence_toReal_eq_zero`.
