<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Counter

**Claim.** For every $r\le n$, starting in state $3$ at clamped input offset $p$, with a unary counter of length $n$, its head at $r-1$ and empty output, the machine reaches after $r+1$ steps state $4$ at the same offset, with the counter unchanged, head at $0$, and output empty.

**Proof.** Induct on $r$. For $r=0$, the counter head is at $-1$, where the unary counter reads no symbol (`satRedCounter_left`). The state-$3$ transition therefore moves the counter head right to $0$, leaves the input position fixed, and enters state $4$. The zero-step and successor-step laws for runs (`runFrom_zero`, `runFrom_succ_eq_step`) reduce this case to that single transition, whose configuration is identified by the silent-move action law (`satDrop_move`) and the fact that a zero input move fixes the input position (`moveInputPos_zero`). For the successor case, the starting head position $(r+1)-1$ equals $r$, and $r<n$ follows from $r+1\le n$. Thus the counter reads true there (`satRedCounter_read`). In state $3$, this makes the machine move its counter head left, remain in state $3$, and keep its input position fixed. The resulting head is $r-1$, so the induction hypothesis applies for the remaining $r+1$ steps. Combining this initial step with those steps by the successor-step run law yields the claimed total of $(r+1)+1$ steps and the final state-$4$ configuration.

**Key facts.** `Complexity.satRedCounter_left`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.satDrop_move`, `Turing.moveInputPos_zero`, `Complexity.satRedCounter_read`.
