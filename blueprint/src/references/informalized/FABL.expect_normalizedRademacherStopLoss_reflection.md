<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.expect_normalizedRademacherStopLoss_reflection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflection Identity for Stop Loss

**Claim.** For the normalized sign sum $R_n$, the uniform expectation of $(R_n(x)-t)^+$ equals $-t$ plus the uniform expectation of $(R_n(x)+t)^+$.

**Proof.** First, reindex the sign-cube average by negation. Since $R_n(-x)=-R_n(x)$ (\texttt{FABL.normalizedRademacherSum\_neg}), this identifies the average of $(t-R_n(x))^+$ with that of $(R_n(x)+t)^+$. Next use the positive-part identity $u^+=u+(-u)^+$ (\texttt{FABL.posPart\_eq\_self\_add\_neg\_posPart}) with $u=R_n(x)-t$. It expresses $(R_n(x)-t)^+$ as $R_n(x)-t+(t-R_n(x))^+$. Averaging, the mean of $R_n$ is zero (\texttt{FABL.expect\_normalizedRademacherSum\_eq\_zero}), so the first two terms average to $-t$. The reflected-average identity supplies the remaining term, proving the formula.

**Key facts.** `FABL.normalizedRademacherSum_neg`, `FABL.posPart_eq_self_add_neg_posPart`, `FABL.expect_normalizedRademacherSum_eq_zero`.
