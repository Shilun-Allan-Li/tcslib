<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.wStep_eq_absStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Circuit Evaluation Steps

**Claim.** For every pair of natural numbers $n,k$ and every function $a\colon\mathbb{N}\to\mathbb{N}$, the word-processing step agrees with the abstract gate-processing step on every bit string and value list.

**Proof.** The two steps are functions of a state consisting of a bit string and a list of values. To prove that they are equal, it is enough to compare their outputs at an arbitrary state $(w,vs)$. The pointwise identity `absStep_eq_wStep` states precisely that the abstract gate step and the word-processing step have the same output there. Reversing the equality gives the stated orientation, and hence the functions agree everywhere.

**Key facts.** `Randomized.PIT.absStep_eq_wStep`.
