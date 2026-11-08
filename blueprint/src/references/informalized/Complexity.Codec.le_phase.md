<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.le_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison phase outcome

**Claim.** If $\mathrm{Pos}\le N_1$, the machine reaches the next phase—$E2$ in step mode and the clearing phase otherwise—without changing the register valuation. If $\mathrm{Pos}>N_1$, it halts with answer $0$. Both runs satisfy the register bound and precondition throughout.

**Proof.** Apply the comparison-loop result (\texttt{le_run}) to the valuation of $R$. Since $T=0$ and all registers are bounded by $B=\mathrm{bnd}(N,y)$, the loop reaches either the clearing phase when $\mathrm{Pos}\le N_1$, or the rejecting state otherwise, with $T$ replaced by $\min(\mathrm{Pos},N_1)$. The register-coordinate facts (\texttt{Regs.val_Pos}, \texttt{Regs.val_N1}, \texttt{Regs.upd_T}) identify this loop conclusion with the displayed fields of $R$.

In the first case, the minimum is $\mathrm{Pos}$, while the initial value of $T$ was zero; the loop's final clearing instruction sets $T$ back to zero. Thus the valuation is again exactly $R$. A single guarded transition then goes from the clearing phase to $E2$ in step mode and to the designated clearing phase otherwise. The initial guard follows from the register bound and the trivial precondition at this instruction (\texttt{gd_of}); reachability concatenation gives the required run (\texttt{Reach.single'}, \texttt{Reach.trans}). In the second case, the loop reaches rejection, and the rejection-to-halt fact gives a run halting with answer $0$ while preserving the guard (\texttt{halt_rej}).

**Key facts.** `Complexity.Codec.le_run`, `Complexity.Codec.Regs.val_Pos`, `Complexity.Codec.Regs.val_N1`, `Complexity.Codec.Regs.upd_T`, `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.gd_of`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.Reach.trans`, `Complexity.Codec.halt_rej`.
