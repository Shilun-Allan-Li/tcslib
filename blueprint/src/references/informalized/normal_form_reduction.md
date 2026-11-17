<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/BackgroundFacts.lean :: normal_form_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of reduction parameters

**Claim.** Given the stated positive parameters and hypotheses, there exist a length $n'$ and positive parameters $\delta',\epsilon'$ satisfying the three displayed bounds.

**Proof.** Choose $n'=0$ and choose $\delta'$ and $\epsilon'$ to equal their respective lower bounds, $\epsilon\delta/(3q^2 2^{q-1})$ and $\epsilon/2^{2q}$. The length bound then holds because $0\le 6n$. Each parameter meets its lower bound by equality. The assumptions $q\ge2$, $\delta>0$, and $\epsilon>0$ make both denominators positive and both chosen parameters strictly positive.

**Caveat.** The supplied Lean proof establishes only this existential numerical statement; it does not construct or prove properties of a normally decodable code.
