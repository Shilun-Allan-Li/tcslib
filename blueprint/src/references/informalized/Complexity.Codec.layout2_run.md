<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean :: Complexity.Codec.layout2_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the second layout stage

**Claim.** Under the stated encoding and register hypotheses, either the specified length and bit condition on $w'$ holds and the program reaches the input-checking stage with the stated register values, or that condition fails and the program halts with answer false. In either case its run respects the register bound and safety condition before its endpoint.

**Proof.** Set $n=|x|$, $b=2n+2|w|+4$, $e=b+4W(N)s+2W(N)$, and $f=e+2w_P(n)$. The nested pair encoding gives $|y|=b+2|w'|+2+|r|$. The proof also records the available bound on $b+2W(N)(2s+1)$ from $s\le2|y|$, and the binary-width estimate $w_P(n)\le n+1$.

1. Starting at the copying stage for $E_2$, the program copies the base value $b$ into $E_2$, copies $s$ into $T$, scales $E_2$ by $4W(N)s$, and adds $2W(N)$ more. It then copies the resulting $e$ into $F_2$, copies $w_P(n)$ into $T$, scales $F_2$ by two, and clears and sets $U$ to $f+4$. The copy, scaling, and increment runs (`cp_run`, `sc_run`, and `ic_run`), together with the single-step reachability rule, establish this run and its intermediate register values. The bound on the scaled values ensures these runs stay within the global register limit.

2. At the length check, the program compares $U=f+4$ with $P$. Using the given formula for $P$, this check passes exactly when $|w'|=W(N)(2s+1)+w_P(n)+1$. If the length equality fails, the program goes directly to rejection and halts with false (`halt_rej`). If it holds, the position $f$ in the encoded input is exactly the position corresponding to $W(N)(2s+1)+w_P(n)$ in $w'$; this follows from the nested pair layout (`getD_w2`). Thus the bit oracle at that input position tests the specified bit of $w'` (`orc_bit`). If that bit is false, the program rejects and halts with false. If it is true, it clears $Q_1$, copies $f$ into it, and begins the position-decoding routine.

3. In the successful branch, let $p$ be the first $w_P(n)$ bits of $w'$ after dropping its first $W(N)(2s+1)$ bits. The position-decoding routine reads these bits from the encoded input and accumulates their binary value in $\mathrm{Pos}_2$. The offset calculation follows from the nested encoding, and `getD_w2` identifies each encoded input bit with the corresponding bit of $p$. The binary-value bound `bitsVal_lt_two_pow`, together with the estimate on $2^{w_P(n)}$ (`two_pow_bits_le`), supplies the bounded suffix values needed by `dc_run`. That routine therefore reaches the input-checking stage with $\mathrm{Pos}_2=\mathrm{bitsVal}(p)$ and the other registers as prescribed. Simplifying the register updates gives exactly the stated layout record.

Throughout, each invoked run preserves the guarded reachability condition, and concatenating runs preserves reachability (`Reach.trans`); equality casts align their register records (`Reach.cast`). The assumed bounds, the layout bound (`bnd_ge`), and the binary-width estimates ensure the register limits required at each stage.

**Key facts.** `Turing.length_pairEncode`, `Complexity.Codec.bnd_ge`, `Complexity.Codec.wP_le`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.cp_run`, `Complexity.Codec.sc_run`, `Complexity.Codec.ic_run`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.Reach.trans`, `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.getD_w2`, `Complexity.Codec.orc_bit`, `Complexity.Codec.halt_rej`, `Complexity.Codec.bitsVal_lt_two_pow`, `Complexity.Codec.two_pow_bits_le`, `Complexity.Codec.dc_run`, `Complexity.Codec.Regs.val_E2`, `Complexity.LogProg.vword_whole₁`.
