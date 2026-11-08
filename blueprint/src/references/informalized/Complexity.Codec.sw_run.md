<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.sw_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded register-program scan

**Claim.** Under the stated hypotheses, the codec program either processes a canonical, sufficiently short suffix and reaches its designated next state with the suffix's binary value in $S$, or detects failure of that suffix condition and halts with answer false; the guard holds throughout.

**Proof.** Set $B=(8W+8)(|y|+1)$. First, the program copies the starting pointer into $Q1$, copies $L$ into $Cap$, and scans the suffix $y[p:]$ (`cp_run`, `ct_run`). The scan either reports that its length is at most the binary expansion length of $|y|$ and that its final bit is $1$ (with the empty suffix allowed by the corresponding convention), or sends execution to rejection. The latter criterion is equivalent to the stated conjunction of canonicality and the length bound, by the characterization of `Canon` using the last-bit default (`canon_of_getLastD`, `getLastD_of_canon`).

In the successful case, the program copies the endpoint into $Q2$ and decodes the suffix into $S$. The decoding routine's hypotheses are met because the suffix has the required width and the input positions agree with its bits; the binary value of every suffix segment stays within $B$ by `bitsVal_le_of_width`, while the positions in the input are bounded using the elementary estimate $2|y|\le B$. Thus `dc_run` yields $Q2=p$ and $S=\mathrm{bitsVal}(y[p:])$. Register copying and the reach casts align the intermediate register assignments with the asserted final assignment. The initial copy, scan, endpoint copy, and decoding reaches compose by `Reach.trans`; all intermediate and final register assignments satisfy the guard bound.

In the failure case, the scan goes to the reject state. The composed reach therefore gives a guarded halt with answer false (`halt_rej`). The bound on the input length used in the scan follows from `length_le_bnd`.

**Key facts.** `Complexity.Codec.length_le_bnd`, `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.cp_run`, `Complexity.Codec.ct_run`, `Complexity.Codec.canon_of_getLastD`, `Complexity.Codec.getLastD_of_canon`, `Complexity.Codec.bitsVal_le_of_width`, `Complexity.Codec.dc_run`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.Reach.trans`, `Complexity.Codec.halt_rej`.
