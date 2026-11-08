<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.inpS_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translation of Input-Position Sources

**Claim.** Under the register-index and layout-source hypotheses, translating every descriptor in the input-position source list yields precisely the canonical source list for position $p$ at time $t$.

**Proof.** First split the source list into its fixed input-position descriptors and its previous-snapshot tail. The tail translates to the canonical previous-snapshot sources by `Complexity.UTab.psnS_toBitSrc`, using the hypothesis that the $LB$ register is $t$ times the configuration stride. For the fixed descriptors, the Boolean flags for $p=0$, $p=1$, and $p=N+1$ translate directly to the corresponding boundary indicators. The remaining flag, that $p$ lies strictly between the two boundary positions, is equivalent to $1\le p\le N$; hence the selected layout source is exactly the stipulated source from $\ell$ in that range and the false constant outside it. The neighboring previous-input descriptors use the $Q$ register when $t\ne0$, while the current-position descriptors use the $I$ register. Substituting their assumed encoded indices into the source translation formulas gives the canonical indices for the previous and current neighboring positions. At $t=0$, or at either boundary position, the corresponding guard instead selects the false constant; the bound $p<N+2$ ensures these cases exhaust the relevant boundary possibilities. These case checks establish equality of the fixed prefixes, and together with the tail equality give the claimed equality of lists.

**Key facts.** `Complexity.UTab.psnS_toBitSrc`.
