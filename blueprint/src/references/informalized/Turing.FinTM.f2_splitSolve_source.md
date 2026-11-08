<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSolve_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Solver

**Claim.** Under the stated assumptions on the source machine and its time bound, there is a finite Boolean Turing machine that computes the encoded split selected by the length equation, returning the empty word if no such split exists, in polynomial time; its space usage at every time is polynomially bounded as stated.

**Proof.** The construction reduces the claim to the general split-body solver theorem (`f2_splitSolve_of_body`). Use the split-body machine built from the source machine, with its designated anchor state and with the stated polynomial envelope constant. From the empty input word, its start configuration is the anchor configuration with empty state word (`f2_splitBody_start`), so the required start phase takes zero steps. For a proposed prefix state word $s$ on input $w$, the round simulation lemma (`f2_splitBody_round`) converts the assumed source computation into a split-body round: the source machine halts with the prescribed unary output, and the split-body round has no intermediate return to the anchor. Its duration is bounded by the source running time plus the overhead $5|s|+3|w|+20$. Since $|s|\le |w|+1$ and the source running time satisfies the assumed bound, the polynomial envelope inequality (`f2_splitBody_envelope`) bounds this entire round by the chosen constant times $(|w|+1)^{e+1}$. The output length condition for acceptance is exactly the condition used by the round lemma, because the source output has length $C(|s|+1)^e$. These start and round bounds are precisely the hypotheses of the general split-body solver theorem, which yields the machine computing the specified split in time $c(|w|+1)^{e+2}$ and bounds its space at every time by $c(|x|+1)^{e+1}$.

**Key facts.** `Turing.FinTM.f2_splitBody_start`, `Turing.FinTM.f2_splitBody_round`, `Turing.FinTM.f2_splitBody_envelope`, `Turing.FinTM.f2_splitSolve_of_body`.
