<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.exists_FinNDTM_of_eff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fair-Random Simulation of a Verifier

**Claim.** Every efficient bit-valued verifier M can be implemented by a finite nondeterministic machine that halts on all choice words of a polynomially bounded length, has exactly the same output-bit probabilities as M on uniformly random strings of the prescribed length, and on each choice word outputs M(x,u) for some string u of that length.

**Proof.** Start with the masked-selection machine (`Randomized.exists_FinNDTM_maskSelect_of_eff`). For each x it provides an offset and a mask whose number of true entries is polyLen(a,k,|x|), together with a machine that halts on every full-length choice word and outputs M(x,u), where u is the mask-selected portion. The full-length word is long enough to contain the offset and the mask.

For each output bit b, the event that the machine outputs b agrees on every choice word with the event that M(x,u)=b. Converting fair choice words to functions from the finite index set and using this pointwise equivalence preserves their uniform probabilities (`Randomized.randProb_congr`). The distribution of the mask-selected segment of a uniform full-length word is uniform over words of length equal to the number of true mask entries (`Randomized.randProb_maskSelect_drop_take`); the required fit inequality justifies discarding the unused positions. Since that number is polyLen(a,k,|x|), this is exactly M's output probability on uniform strings of the specified length.

Finally, the selected word has that prescribed length. Every finite Boolean word of that length can be represented as List.ofFn for a function on the corresponding finite index set (`Randomized.exists_ofFn_eq`). Substituting this representation into the machine's output identity proves that each individual choice word produces M(x,u) for some u of the required length.

**Key facts.** `Randomized.exists_FinNDTM_maskSelect_of_eff`, `Randomized.randProb_congr`, `Randomized.randProb_maskSelect_drop_take`, `Randomized.exists_ofFn_eq`.
