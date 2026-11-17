<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingClosedOn_erase_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure After Removing a Matched Pair

**Claim.** Removing a vertex and its matching partner from a set closed under taking matching partners leaves a set that is still closed under taking matching partners.

**Proof.** Let $x$ remain after the two erasures, and write $m(x)$ for its matching partner. Closure of the original set ensures $m(x)$ was in that set. To show it survives both erasures, first suppose $m(x)$ were the removed vertex $v$. Applying the partner map to this equality and using that the map is an involution gives $x=m(v)$; this is impossible because $x$ survived the erasure of $m(v)$. Next suppose $m(x)=m(v)$. Applying the partner map gives $x=v$, also impossible because $x$ survived the erasure of $v$. Thus $m(x)$ remains, proving closure. The fact that taking a matching partner twice returns the original vertex is the involutivity property (\texttt{FABL.graphPartiteMatchingPartner_involutive}).

**Key facts.** `FABL.graphPartiteMatchingPartner_involutive`.
