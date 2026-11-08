<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of outside agreement

**Claim.** If $m_2$ agrees with $m_1$ outside $s$ and $m_3$ agrees with $m_2$ outside $s$, then $m_3$ agrees with $m_1$ outside $s$.

**Proof.** At any address outside $s$, the second assumption gives $m_3(a)=m_2(a)$, while the first gives $m_2(a)=m_1(a)$. Transitivity of equality yields $m_3(a)=m_1(a)$ at every such address.
