<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.PH_eq_SigmaP_two_of_inBPP_SAT3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Second-Level Collapse of PH

**Claim.** If $3$-CNF satisfiability belongs to $\mathrm{BPP}$ as defined using the polynomial-time verifier model, then $\mathrm{PH}=\Sigma_2^P$.

**Proof.** Let $L$ be any language in $\mathrm{NP}$. Since $3$-CNF satisfiability is NP-hard, $L$ polynomial-time reduces to it ($\mathrm{SAT3\_NPHard}$). Bounded-error probabilistic membership transfers backward along this reduction, so $L$ is in the verifier-model $\mathrm{BPP}$ class ($\mathrm{InBPP.of\_polyTimeReducible}$). Adleman’s theorem converts this probabilistic computation into a polynomial-size circuit representation ($\mathrm{adleman\_polyTime}$); the equivalence between the circuit class and its language characterization yields $L\in\mathrm{PPoly}$ ($\mathrm{BoolCircuit.mem\_PPoly\_iff}$). Thus $\mathrm{NP}\subseteq\mathrm{PPoly}$, and the collapse theorem under this containment gives $\mathrm{PH}=\Sigma_2^P$ ($\mathrm{PH\_eq\_SigmaP\_two\_of\_NP\_subset\_PPoly}$).

**Key facts.** `Complexity.SAT3_NPHard`, `Randomized.InBPP.of_polyTimeReducible`, `Randomized.adleman_polyTime`, `BoolCircuit.mem_PPoly_iff`, `Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`.
