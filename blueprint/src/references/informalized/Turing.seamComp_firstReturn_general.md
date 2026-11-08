<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_firstReturn_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Early Visit to the Second Exit State

**Claim.** Before time $T_1+1+T_2$, the seam-composed run from the left-embedded initial configuration never has state $\mathrm{inr}(q_2)$.

**Proof.** Fix $t<T_1+1+T_2$ and split according to whether $t\le T_1$. In the first case, the run-through-the-left-component theorem (`seamCompTM_runFrom_left`) identifies the seam run at time $t$ with the left embedding of the $M_1$ run. Its state is either absent or lies in the left summand, so it cannot equal $\mathrm{inr}(q_2)$. If instead $t>T_1$, write $t=T_1+1+u$, where $u=t-(T_1+1)$. The run-through-the-right-component theorem (`seamCompTM_runFrom_right`) identifies the configuration at that time with the right embedding of the $M_2$ run from the entry-renamed $c_1$, after $u$ steps. The time bound gives $u<T_2$. Thus a state equal to $\mathrm{inr}(q_2)$ would, by injectivity of the right-summand embedding, give state $q_2$ in that $M_2$ run, contrary to the assumed avoidance before $T_2$.

**Key facts.** `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM_runFrom_right`.
