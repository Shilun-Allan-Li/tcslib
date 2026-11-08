<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean :: Complexity.LogProg.npre_of_npreS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer to Banked Preconditions

**Claim.** Under the stated space bounds, a configuration satisfying the nondeterministic precondition and the register bit-length bounds also satisfies the precondition for the banked decider machine, with language indicators as its oracles and space bound $B$.

**Proof.** The proof unfolds the two preconditions and separates halted configurations from live ones. A halted configuration satisfies the target precondition directly. For a live configuration, inspect its current instruction. For register equality and the three input-comparison instructions, the target precondition is exactly the corresponding condition already present in the source precondition. All other non-call instructions impose no additional condition.

It remains to handle a decider call. The source precondition gives both that the argument registers are distinct and that the original decider has a clean halting run on the virtual input, with the oracle's answer and its stated space bound. The bank simulation theorem (`bank_cleanRun`) provides a corresponding clean run of the banked machine, with space at most the maximum of the selected decider's space bound on that input length and $1$. To apply the assumed uniform bound, first bound the virtual input length. Each argument's bit word has length at most $W_d$: its length is no greater than the length of the bits of the register value plus one (`length_bits_mono`), which is bounded by hypothesis. The virtual input length estimate (`length_callSegs_le`), using distinctness of the argument registers, is therefore at most $2|x|+2+m(2W_d+2)$. The assumed bound on $s_j$ applies at this length, and $1\le B$ handles the other term in the maximum. Thus the banked clean run also fits within space $B$ (`cleanRun_mono`), establishing the target call precondition.

**Key facts.** `Complexity.LogProg.bank_cleanRun`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.length_callSegs_le`, `Complexity.LogProg.cleanRun_mono`.
