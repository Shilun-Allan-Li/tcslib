<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPoly.lean :: Complexity.P_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Has Polynomial-Size Circuits

**Claim.** Every language decidable in polynomial time has a family of fan-in-two Boolean circuits deciding it, with constants $a,k \in \mathbb{N}$ such that the circuit on inputs of length $n$ has size at most $a(n+1)^k$.

**Proof.** 1. By the polynomial-time characterization with an explicit polynomial bound, choose natural numbers $C,d$ and a machine $M_0$ deciding $L$ in time $C(n+1)^d$ (\(\texttt{Complexity.mem\_P\_iff}\)). Increase the bound to $(C+1)(n+1)^{d+1}$: since $n+1 \ge 1$, its $(d+1)$st power is at least its $d$th power, and $C \le C+1$. The original machine therefore still decides $L$ within this larger bound. The polynomial time-constructibility fact supplies a time-constructible bound of this form (\(\texttt{Complexity.timeConstructible\_poly}\)).

2. Apply the oblivious simulation theorem to obtain an oblivious machine $M$ and a constant $c$ that decide $L$ within $T'(n)=c((C+1)(n+1)^{d+1}+1)^2$ (\(\texttt{Complexity.oblivious\_of\_mem\_DTIME}\)). Obliviousness makes the computation layout depend only on input length, allowing a circuit to encode the computation tableau for each length. The tableau evaluation theorem says that this circuit, on each input, outputs the decision of $M$ (\(\texttt{Complexity.tableauCircuit\_eval\_of\_decidesInTime}\)); the tableau construction is fan-in two (\(\texttt{Complexity.tableauCircuit\_isFaninTwo}\)).

3. The tableau circuit has size $n+2+(T'(n)+1)W$, where $W$ is the tableau width (\(\texttt{Complexity.tableauCircuit\_size}\)). The polynomial size estimate bounds this quantity by $(2+W+c(C+2)^2W)(n+1)^{2(d+1)}$ (\(\texttt{Complexity.tableau\_size\_le}\)). Hence the family has polynomial size with the claimed form. Finally, the characterization of a family’s language by its circuit evaluations (\(\texttt{BoolCircuit.DAGCircuitFamily.mem\_language\_iff}\)), together with the tableau evaluation result, identifies that family’s language with $L$.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.timeConstructible_poly`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.oblivious_of_mem_DTIME`, `Complexity.tableauCircuit_isFaninTwo`, `Complexity.tableauCircuit_size`, `Complexity.tableau_size_le`, `Complexity.tableauCircuit_eval_of_decidesInTime`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
