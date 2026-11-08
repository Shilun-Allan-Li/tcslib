<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.g_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Initial Configuration

**Claim.** If all 17 register values in $S$ are at most $B$ and the memory head satisfies $0\le p\le P$, then the configuration at any label, with registers from $S$, empty answer, memory $M$, and head at $p$, satisfies $G(x,B,P)$.

**Proof.** By definition, the register part of $G$ requires both the program precondition and a bound of $B$ on every register. The universal precondition lemma for this program supplies the first condition (`Complexity.LogProg.ExpBFS.preS_A`). The componentwise bounds in $hbd$ give the second: each register in the configuration is the corresponding coordinate of $S$, and the register-vector bound follows from `St.Bd.toV`. The remaining conditions of $G$ are exactly the assumed bounds on $p$.

**Key facts.** `Complexity.LogProg.ExpBFS.preS_A`, `Complexity.LogProg.ExpBFS.St.Bd.toV`.
