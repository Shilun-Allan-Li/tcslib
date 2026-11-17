<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_pair_triple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tracked slots are not selected

**Claim.** For every source tape and tracked component, the partial selector for argument and capture roles is undefined at that component's physical call-layout index.

**Proof.** The selector is defined only at the argument index $0$ and the capture index $1+3k$. A tracked index has one of the forms $1+i$, $1+k+i$, or $1+2k+i$, with $0\le i<k$. Each is positive, so it is not the argument index; and each is strictly less than $1+3k$, so it is not the capture index. The selector is therefore undefined at every tracked slot.
