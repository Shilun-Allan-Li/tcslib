<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.HALT_NPHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP-Hardness of the Halting Language

**Claim.** For every machine representation scheme $c$, every language in NP is polynomial-time many-one reducible to the language of strings on which the halting function of $c$ returns true.

**Proof.** Fix an NP language $L$. By the inclusion of NP in EXP (NP_subset_EXP), choose an exponential-time decider $D$ for $L$, with its time bound of the form used in the EXP definition. Convert $D$ to an equivalent one-work-tape Boolean machine $M$ (Turing.FinTM.one_work_tape_binary), and choose a code machine $S$ for $M$ (Turing.exists_codeTM). Map an input $x$ to the pairing encoding of $c$'s encoding of $S$ with $x$. This map is polynomial-time computable for the fixed prefix $c.encode S$ (Complexity.fixedPair_polyTime). The defining property of machine codes gives $c.decode (c.encode S)=S$ (Turing.MachineCode.decode_encode). Consequently, the halting characterization on encoded pairs (Complexity.HALT_pairEncode_eq_true_iff) says that the image is accepted exactly when the machine represented by $S$ produces some output on $x$ within finite time. Since $S$ represents $M$, this is equivalent to $M$ accepting $x$; the acceptance-machine characterization (Complexity.acceptTM_halts_iff), together with the fact that $D$ computes the indicator of $L$, identifies this with $x\in L$. The map is therefore a polynomial-time many-one reduction from $L$ to the halting language.

**Key facts.** `Complexity.NP_subset_EXP`, `Turing.FinTM.one_work_tape_binary`, `Turing.exists_codeTM`, `Complexity.fixedPair_polyTime`, `Turing.MachineCode.decode_encode`, `Complexity.HALT_pairEncode_eq_true_iff`, `Complexity.acceptTM_halts_iff`.
