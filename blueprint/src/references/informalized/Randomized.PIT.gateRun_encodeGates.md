<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.gateRun_encodeGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Encoded Gate List

**Claim.** For a gate list whose arithmetic gates refer only to earlier positions, running the evaluator on its encoding produces the state encoding with terminal word $[0]$ and the successive gate values modulo $\mathrm{bitsVal}(R)+1$.

**Proof.** Represent the evaluator run by the abstract parser iterated for the length of the encoded gate string (`gateRun_eq`). The parser theorem for encoded gate lists says that after one step per gate, the remaining word is $[0]$ and the values are exactly the successive evaluation (`iterate_absStep_encodeGates`). Its reference hypothesis holds here: the given bounds are relative to the gate-list position, and the initial value list is empty, so those are precisely the parser's bounds. The run has more iterations than the number of gates (`length_encodeGates`); after reaching $[0]$, further abstract steps fix the state. Thus the additional iterations do not change the resulting word or values, and the run representation gives the claimed encoded state.

**Key facts.** `Randomized.AlCircuit.length_encodeGates`, `Randomized.PIT.gateRun_eq`, `Randomized.PIT.iterate_absStep_encodeGates`.

**Caveat.** The supplied name `Randomized.AlCircuit.length_encodeGates` appears inconsistent with the displayed namespace `Randomized.AlgCircuit`; the mathematical fact used is the stated encoded-length bound.
