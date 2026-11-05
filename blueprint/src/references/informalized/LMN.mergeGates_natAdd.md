<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: LMN.mergeGates_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Merged gate array on a right-hand index

**Claim.** Let $g_1 : \mathrm{Fin}\,m_1 \to \alpha$ and $g_2 : \mathrm{Fin}\,m_2 \to \alpha$ be gate arrays, and let $i \in \mathrm{Fin}\,m_2$. Then their merged array, viewed as a function on $\mathrm{Fin}(m_1 + m_2)$, takes the value $g_2(i)$ at the index $m_1 + i$.

**Proof.** Recall how the merged array is defined: at an index $j \in \mathrm{Fin}(m_1 + m_2)$ it inspects the underlying natural number $j.\mathrm{val}$ and returns
\[
\mathrm{mergeGates}\,g_1\,g_2\,(j) \;=\;
\begin{cases}
g_1\big(\langle j.\mathrm{val}\rangle\big), & \text{if } j.\mathrm{val} < m_1,\\[2pt]
g_2\big(\langle j.\mathrm{val} - m_1\rangle\big), & \text{otherwise.}
\end{cases}
\]

The index in question is $m_1 + i$, encoded as the element of $\mathrm{Fin}(m_1 + m_2)$ whose underlying value is $m_1 + i.\mathrm{val}$ (this is what `Fin.natAdd m₁ i` denotes). The whole content of the proof is to determine which branch of the definition fires.

Since $i.\mathrm{val} \ge 0$, we have $m_1 + i.\mathrm{val} \ge m_1$, so the guard $m_1 + i.\mathrm{val} < m_1$ is false (this is the single arithmetic fact the proof isolates and discharges by `omega`). Hence the definition selects its second branch and returns
\[
g_2\big(\langle (m_1 + i.\mathrm{val}) - m_1\rangle\big).
\]
Finally $(m_1 + i.\mathrm{val}) - m_1 = i.\mathrm{val}$, so the argument is exactly $i$, giving $g_2(i)$. The reduction of the subtraction and the identification of the resulting $\mathrm{Fin}$ element with $i$ are routine bookkeeping that the simplifier handles once the false guard is supplied.
