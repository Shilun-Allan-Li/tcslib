<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.workOK_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Work Tape Consistency Check

**Claim.** If the answer table agrees with the machine’s actual tabulated answers throughout the stated time and address range, then under the given bounds the work-tape consistency check at time $t$, tape $h$, and the sign determined by $e<0$ evaluates to true.

**Proof.** First establish two interpretations of the encoded tape symbols at the current and next times. For the current head-relative address, the table’s symbol encoding equals the actual symbol at offset $e$; for the neighboring address, it equals the actual symbol at offset $e+1$. The answer-table agreement gives these identifications via the symbol-value lemma ( `Complexity.Meyer.sv_true_some`), and the signed-address identities ( `Complexity.Meyer.edge_c1`, `Complexity.Meyer.edge_c2`) convert the encoded natural addresses back to $e$ and $e+1$. The time and address bounds ensure the table-agreement hypothesis applies at both times and both addresses.

Unfold the work-consistency check and substitute these interpretations, along with the endpoint identities for its zero-address conditions ( `Complexity.Meyer.edge_E0`, `Complexity.Meyer.edge_E1`) and the compatibility of address selection with a conditional choice ( `Complexity.Meyer.avOf_ite`). The check now compares actual tape symbols before and after one machine step. The successor-time run is one step from the time-$t$ configuration ( `Turing.MultiTapeTM.runFrom_succ_eq_step'`), and the read-symbol encoding reduces to the symbols read from that configuration ( `Complexity.Meyer.symvA_NumVal`). The step’s effect on a work-tape cell is described by the tape-update rule ( `Complexity.Meyer.RW_step`).

If the current configuration is halting, the tape is unchanged, so the comparison holds. Otherwise inspect the work head’s movement. With zero movement, the same cell is compared. With positive movement, the next head-relative cell is the old cell one position ahead, as expressed by the positive-move tape rule. With negative movement, it is the old cell one position behind unless the move would pass the leftmost encoded address; at that boundary the check instead compares against the written symbol. In each case the selected comparison is exactly the actual transition’s tape update, so the Boolean check is true.

**Key facts.** `Complexity.Meyer.sv_true_some`, `Complexity.Meyer.edge_c1`, `Complexity.Meyer.edge_c2`, `Complexity.Meyer.edge_E0`, `Complexity.Meyer.edge_E1`, `Complexity.Meyer.avOf_ite`, `Complexity.Meyer.symvA_NumVal`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.RW_step`.

**Caveat.** The proof’s final simplification of the negative-movement boundary case depends on the detailed behavior of `ruleW`, which is not included among the supplied upstream statements; the route is clear, but that case cannot be fully reconstructed from the supplied material alone.
