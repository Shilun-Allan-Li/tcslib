<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.TMSAT_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# TMSAT Belongs to NP

**Claim.** For an effective machine-code scheme whose canonizer computes serialization in polynomial time, TMSAT belongs to NP.

**Proof.** 1. Obtain a quantitative universal machine: it simulates a decoded machine on a given input for a specified number of steps, producing an affirmative result when the computation exists and a negative result when none does ($\texttt{timed_universal_quantitative}$). The polynomial bound on the canonizer's running time yields a polynomial simulation budget for the encoded requests ($\texttt{tmsat_simulation_budget}$); the resulting simulator can be treated as giving an answer in either case ($\texttt{tmsat_simulator_total}$).

2. Show the language of valid TMSAT certificates is in polynomial time. On a well-formed request, assemble the simulator input from the time bound, machine code, and paired input, and run the simulator within the polynomial budget. The bounds on the extracted code and clock ensure the chosen budget applies ($\texttt{tmsat_good_bounds}$). On malformed requests, return the fixed negative answer. The request assembly is polynomial-time computable ($\texttt{tmsat_request_poly}$), and composing it with the simulator gives a polynomial-time computation of the verifier's result; composing with the fixed equality check recognizes acceptance ($\texttt{exists_comp_on_image}$ and $\texttt{tmsat_pt_eq}$). The result-acceptance lemma identifies this output test with membership in the verifier language ($\texttt{tmsat_result_accept}$), and the polynomial-time characterization of $\mathsf P$ then places that verifier in $\mathsf P$ ($\texttt{mem_P_iff}$).

3. The certificate-equivalence lemma states that an instance belongs to TMSAT exactly when it has an accepting verifier certificate of length one more than the instance length ($\texttt{tmsat_certificate_equiv}$). This is an NP certificate bound with exponent one and constant one. Therefore TMSAT belongs to NP.

**Key facts.** `Complexity.timed_universal_quantitative`, `Complexity.tmsat_simulation_budget`, `Complexity.tmsat_simulator_total`, `Complexity.tmsat_good_bounds`, `Complexity.tmsat_request_poly`, `Turing.FinTM.exists_comp_on_image`, `Complexity.tmsat_pt_eq`, `Complexity.tmsat_result_accept`, `Complexity.mem_P_iff`, `Complexity.tmsat_certificate_equiv`.
