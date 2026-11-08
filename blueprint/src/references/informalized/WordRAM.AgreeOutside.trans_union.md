<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.trans_union -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity over a union

**Claim.** If $m_2$ agrees with $m_1$ outside $s$ and $m_3$ agrees with $m_2$ outside $t$, then $m_3$ agrees with $m_1$ outside $s\cup t$.

**Proof.** First enlarge the exceptional set in the agreement between $m_1$ and $m_2$ from $s$ to $s\cup t$, using the fact that agreement outside a set persists when that set is enlarged (WordRAM.AgreeOutside.mono). Do the same for the agreement between $m_2$ and $m_3$, enlarging $t$ to $s\cup t$. Both equalities now hold at every address outside the union. Transitivity of outside agreement (WordRAM.AgreeOutside.trans) combines them to give the desired agreement.

**Key facts.** `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.trans`.
