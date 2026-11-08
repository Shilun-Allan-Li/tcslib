<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.candidate_iff_cast_le_threshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate size threshold equivalence

**Claim.** For positive natural $w$ and natural $k$, the inequality $1-(1-2^{-w})^k\le 1/2$ holds exactly when $k\le \log 2/[-\log(1-2^{-w})]$.

**Proof.** Set $x=2^{-w}$, $q=1-x$, and $L=-\log q$. The base interval fact (`criticalBase_mem_Ioo`) gives $0<q<1$, and the positivity fact (`criticalLog_pos`) gives $L>0$. Thus logarithms preserve order on the positive quantities involved, and division by $L$ preserves the inequality direction. The candidate inequality is equivalent to $1/2\le q^k$. Taking logarithms and using $\log(q^k)=k\log q$ and $\log(1/2)=-\log 2$ turns this into $kL\le\log 2$, which, since $L>0$, is equivalent to $k\le\log 2/L$. Reversing these equivalences proves both directions.

**Key facts.** `FABL.criticalBase_mem_Ioo`, `FABL.criticalLog_pos`.
