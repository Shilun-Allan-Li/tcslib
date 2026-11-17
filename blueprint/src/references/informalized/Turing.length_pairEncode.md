<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.length_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a paired encoding

**Claim.** Encoding bit strings $x$ and $y$ by doubling $x$, inserting the separator $01$, and appending $y$ gives a string of length $2|x|+2+|y|$.

**Proof.** Rewrite the encoding as $\mathrm{dbl}(x)++[0,1]++y$ using the description of the paired encoding (`pairEncode_eq_dbl`). Length is additive under concatenation; the doubled part has length $2|x|$, and the separator has length two by the length-of-doubling result. Adding these lengths gives the stated formula.

**Key facts.** `Turing.pairEncode_eq_dbl`.
