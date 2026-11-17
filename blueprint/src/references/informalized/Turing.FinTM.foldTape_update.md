<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldTape_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folded Writes Commute with Tape Updates

**Claim.** For a tape $t\colon\mathbb{Z}\to\operatorname{Option}(\Gamma)$, position $z\in\mathbb{Z}$, and symbol $a\in\operatorname{Option}(\Gamma)$, updating the folded tape at the folded position of $z$ by writing $a$ on the side determined by $z$ gives the folded tape obtained by updating $t$ at $z$ with $a$.

**Proof.** Compare the two tape functions at an arbitrary folded position $p$. The folded position of $z$ is nonnegative (`foldPos_nonneg`), so its folded cell can be unpacked after packing (`foldUnpack_pack`). If $p=\varphi(z)$, the update changes this cell. When $z\ge0$, the selected side is the first entry, corresponding to the original position $z$; the other entry corresponds to $-z-1$ and is unaffected. When $z<0$, the selected side is the second entry, again corresponding to $z$, while the first entry corresponds to the distinct position $-z-1$. Thus the cell agrees with folding the tape updated at $z$. If $p\ne\varphi(z)$, its folded cell is not changed by the left-hand update. For a nonnegative $p$, neither original position represented there, $p$ or $-p-1$, equals $z$, so the original tape update does not affect that folded cell either. For negative $p$, the folded tape is absent on both sides. This proves equality at every position.

**Key facts.** `Turing.FinTM.foldPos_nonneg`, `Turing.FinTM.foldUnpack_pack`.
