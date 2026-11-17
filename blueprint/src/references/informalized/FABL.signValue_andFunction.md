<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.signValue_andFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-valued formula for the AND function

**Claim.** With $-1$ encoding True, the real value of $\operatorname{AND}_w(x)$ is $1-2\prod_{i\in\mathrm{Fin}(w)}(1-\operatorname{signValue}(x_i))/2$.

**Proof.** Split into two cases. If every coordinate of $x$ is $-1$, then the AND value is $-1$. Each factor $(1-\operatorname{signValue}(x_i))/2$ equals $1$, so their product is $1$; the right side is therefore $1-2=-1$, as required. Otherwise some coordinate $x_j$ is not $-1$. Since a sign is either $-1$ or $1$, that coordinate must be $1$, making its factor $(1-\operatorname{signValue}(x_j))/2$ zero. The product is zero, while the AND value is $1$, so both sides equal $1$. The values of the two constant signs under $\operatorname{signValue}$ are supplied by $\mathrm{signValue\_neg\_one}$ and $\mathrm{signValue\_one}$.

**Key facts.** `FABL.signValue_neg_one`, `FABL.signValue_one`.
