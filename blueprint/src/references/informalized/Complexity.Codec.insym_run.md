<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean :: Complexity.Codec.insym_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol simulation

**Claim.** Under the stated register bounds and initial register conditions, the step-mode program reaches the clearing stage with the input symbol at position $R.\mathrm{Pos}$ encoded in $Z$, some bounded value in $U$, and the original $A,B$ copied into $Q_3,Q_4$, while respecting the safety and register bounds throughout.

**Proof.** Put $B=(8W(N)+8)(|y|+1)$. The proof first establishes that $|y|=2|x|+2+|r|$ and that $|y|\le B$. It then treats the three possible positions separately. If $R.\mathrm{Pos}=0$, the program takes the zero-position branch directly to the copying stage; choose $u=R.U$. If $R.\mathrm{Pos}=|x|+1$, the comparison with $N_1=|x|+1$ likewise goes straight to copying, again with $u=R.U$. In both cases, the input-symbol convention gives no symbol, so $Z=0$ is the required encoding.

In the remaining case, the program copies $R.\mathrm{Pos}$ to $T$, decrements it, clears $U$, and scales the resulting value by two. The scaling run therefore reaches the input-reading stage with $U=2(R.\mathrm{Pos}-1)$ and $T=0$. Since $1\le R.\mathrm{Pos}\le |x|$, the pair encoding has the same bit at position $2(R.\mathrm{Pos}-1)$ as $x$ has at position $R.\mathrm{Pos}-1$ (`pe_getD_fst`). The bit oracle returns that bit (`orc_bit`), so the program follows the false or true branch accordingly and increments $Z$ once or twice. These values are precisely the codes of the corresponding Boolean input symbols. Choose $u=2(R.\mathrm{Pos}-1)$; the position bound and the input-length bound on $B$ give $u\le B$.

Finally, in each case, the program copies $A$ and $B$ into $Q_3$ and $Q_4$. The bounded copy routine applies because those destination registers start at zero and the source values are bounded. The individual transitions satisfy the safety guard and register bound, and reachability is preserved when these runs are concatenated; register-value casts identify the resulting state with the specified record update. These facts are supplied by the bounded-register consequence of `Regs.Bd.val_le`, the guarded single-step and reachability composition results (`gd_of`, `Reach.single'`, `Reach.trans`), and `Reach.cast`.

**Key facts.** `Complexity.Codec.length_le_bnd`, `Turing.length_pairEncode`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.gd_of`, `Complexity.Codec.cp_run`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.Reach.trans`, `Complexity.Codec.sc_run`, `Complexity.Codec.pe_getD_fst`, `Complexity.Codec.orc_bit`, `Complexity.LogProg.vword_whole₁`, `Complexity.Codec.Regs.Bd.val_le`.
