<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: BoolCircuit.allOnesFamily_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language of the All-Ones Family

**Claim.** The all-ones circuit family recognizes exactly the Boolean words whose entries are all true.

**Proof.** Fix a word $w$. By the family membership characterization (`BoolCircuit.LayeredCircuitFamily.mem_language_iff`), acceptance means that the circuit assigned at length $|w|$, evaluated on the word’s entries converted to $\mathrm{Fin}(2)$, has output $1$. The family circuit is the all-ones circuit (`BoolCircuit.allOnesFamily_circuit`), whose output is the product of all its input values (`BoolCircuit.allOnesCircuit_eval₁`). A product in $\mathrm{Fin}(2)$ equals $1$ exactly when every factor equals $1$ (`BoolCircuit.prod_fin_two_eq_one_iff`). Under the Boolean-to-$\mathrm{Fin}(2)$ correspondence, a value is $1$ exactly when the original Boolean is true (`finTwoEquiv_symm_eq_one_iff`). Thus acceptance is equivalent to every indexed entry of $w$ being true. The list formulation “every element of $w$ is true” is equivalent to this indexed formulation, so the recognized language is precisely the all-ones language.

**Key facts.** `BoolCircuit.LayeredCircuitFamily.mem_language_iff`, `BoolCircuit.allOnesFamily_circuit`, `BoolCircuit.allOnesCircuit_eval₁`, `BoolCircuit.prod_fin_two_eq_one_iff`, `finTwoEquiv_symm_eq_one_iff`.
