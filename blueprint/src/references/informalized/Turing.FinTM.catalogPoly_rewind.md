<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPoly_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind of One Loop Head

**Claim.** From rewind state $i$ with head $i$ at position $j-1$, after $j+1$ steps the machine reaches advance state $i+1$, with that head at zero, all other positions unchanged, and the output unchanged.

**Proof.** Induct on $j$. At $j=0$, the selected head is at $-1$, so it reads blank; the rewind transition moves it right and enters advance state $i+1$. The movement calculation (`catalogPolyMove_apply`) identifies its new position as zero. For the successor case, the head is at position $j$, which contains a unary mark since $j<q$. The transition therefore moves that head left and remains in rewind state $i$, putting it at $j-1$. The induction hypothesis handles the remaining run and yields the stated final configuration. Each step leaves the output and tape contents unchanged. The run identities split off the first step and identify a zero-step run (`runFrom_succ_eq_step`, `runFrom_zero`).

**Key facts.** `Turing.FinTM.catalogPolyMove_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
