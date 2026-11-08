<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.core_injOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct cores before halting

**Claim.** If a computation first reaches a halting configuration at time $T$, then its cores at any two times $t_1<t_2<T$ are distinct.

**Proof.** Suppose instead that the cores at $t_1$ and $t_2$ agree, and put $p=t_2-t_1>0$. Equal cores determine all subsequent cores (`core_runFrom`): starting from the two configurations and running for the same number of steps preserves core equality. By the decomposition of a run into consecutive segments (`runFrom_add`), this means that for every $r\ge p$, the core at time $t_1+r$ equals the core at time $t_1+(r-p)$. Strong induction on $r$ now shows that the core at time $t_1+r$ equals the core at time $t_1+(r\bmod p)$. For $r<p$ this is immediate; for $r\ge p$, apply the preceding reduction and the induction hypothesis, noting that subtracting $p$ leaves the remainder modulo $p$ unchanged. Take $r=T-t_1$. The resulting remainder is less than $p$, so the corresponding time $t_1+((T-t_1)\bmod p)$ is strictly less than $T$. The core at that time has the same state as the configuration at time $T$, hence is halting. This contradicts the assumption that no time strictly before $T$ is halted.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.core_runFrom`, `Turing.MultiTapeTM.runFrom_add`.
