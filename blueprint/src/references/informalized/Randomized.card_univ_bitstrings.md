<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.card_univ_bitstrings -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Boolean Strings

**Claim.** For every natural number $m$, the set of functions from an $m$-element set to the two-element Boolean set has cardinality $2^m$.

**Proof.** A function on an $m$-element set is determined by one of two Boolean values at each of its $m$ inputs. Thus the number of such functions is $|\{\mathrm{false},\mathrm{true}\}|^m=2^m$, by the finite-function counting formula.
