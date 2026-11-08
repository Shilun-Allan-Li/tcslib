<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.positiveBias_odds_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odds Step for Positive Bias

**Claim.** Let $n\ge2$, and let $f$ be a monotone Boolean function with positive bias $p$ strictly between $0$ and $1$. Choose a coordinate of maximum influence, and let $p'$ be the positive bias after setting that coordinate to $+1$. With $r=\log(n)/(100n)$, one has $(1+2r)p(1-p')\le p'(1-p)$.

**Proof.** Choose a maximum-influence coordinate and abbreviate the original and bribed positive biases by $p$ and $p'$. The maximum-influence bias step (`maximumInfluenceCoordinate_positiveBias_step`) gives $p+2p(1-p)r\le p'$. The bribery rate is positive for $n\ge2$ (`briberyRate_pos`), and both biases lie in $[0,1]$ (`positiveBias_mem_Icc`). In particular, $p'\ge p$, so $1-p'\le1-p$. Multiplying this latter inequality by the nonnegative quantity $2rp$ preserves its direction. Combining it with the bias-step inequality and rearranging yields $(1+2r)p(1-p')\le p'(1-p)$.

**Key facts.** `FABL.maximumInfluenceCoordinate_positiveBias_step`, `FABL.positiveBias_mem_Icc`, `FABL.briberyRate_pos`.
