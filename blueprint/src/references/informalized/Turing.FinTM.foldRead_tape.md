<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldRead_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Folded Tape

**Claim.** For a tape content $t\colon\mathbb{Z}\to\operatorname{Option}(\Gamma)$ and position $z\in\mathbb{Z}$, reading the folded tape at $\varphi(z)$ on the side determined by whether $z\ge 0$ returns $t(z)$.

**Proof.** First, the folded position $\varphi(z)$ is nonnegative (`foldPos_nonneg`), so the folded-tape definition uses the packed cell containing the two entries $t(\varphi(z))$ and $t(-\varphi(z)-1)$. Unpacking this packed cell recovers the original folded symbol (`foldUnpack_pack`). If $z\ge 0$, then $\varphi(z)=z$ and the selected side is the first entry, which is $t(z)$. If $z<0$, then $\varphi(z)=-z-1$ and the selected side is the second entry, namely $t(-\varphi(z)-1)=t(z)$.

**Key facts.** `Turing.FinTM.foldPos_nonneg`, `Turing.FinTM.foldUnpack_pack`.
