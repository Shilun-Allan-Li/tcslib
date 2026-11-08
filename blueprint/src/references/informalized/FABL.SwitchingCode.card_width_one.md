<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.card_width_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-One Switching-Code Count

**Claim.** For every positive integer $k$, there are exactly two switching codes of width one and index $k$.

**Proof.** Write $k=m+1$, which is possible because $k$ is positive. For $m=0$, the recurrence `card_succ` gives two codes directly. For the induction step, suppose the count at index $m+1$ is two. Apply the recurrence at the next index. When the width is one, the binomial terms vanish except for the initial contribution and the first summand; evaluating those terms shows that the count at index $m+2$ equals the count at index $m+1$. It is therefore also two, completing the induction.

**Key facts.** `FABL.SwitchingCode.card_succ`.
