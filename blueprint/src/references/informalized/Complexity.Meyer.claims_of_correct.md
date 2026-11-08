<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.claims_of_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness implies true claims

**Claim.** Under the stated correctness hypotheses, the numerical valuation determined by $A,W,|x|,t,a,j,b$ makes the state-and-read claims at time $t$ true for the machine's actual configuration.

**Proof.** Unpack correctness into its state-query, work-tape-query, and input-query clauses. Evaluating the claims under the numerical valuation turns the state claim into the corresponding answer-table query, and each symbol claim into a symbol query of that table; these evaluations are given by `stA_NumVal` and `symvA_NumVal`.

For the state claim, correctness identifies the answer-table value with the truth value of the assertion that the proposed state-and-output summary equals the actual summary. Hence the state claim holds. For the input symbol, use `cX_zero` to express the zero-offset signed query as the false-sign symbol query, then apply the input-query clause of correctness at offset zero. This identifies the claimed symbol with the actual input symbol read. For each work tape, the same zero-offset conversion and the work-tape clause of correctness at offset zero identify its claimed symbol with the actual read symbol. The required bounds hold because $t<2^W$, and at offset zero the work-tape bound reduces to this time bound.

**Key facts.** `Complexity.Meyer.stA_NumVal`, `Complexity.Meyer.symvA_NumVal`, `Complexity.Meyer.cX_zero`.
