<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_insert_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean change from adding a bribed coordinate

**Claim.** For monotone $f$, the mean after bribing coordinates in $J\cup\{i\}$ to $1$ equals the mean after bribing $J$ to $1$, plus the influence of coordinate $i$ on the function already bribed on $J$.

**Proof.** Bribing the coordinates in $J\cup\{i\}$ to $1$ is the same as first bribing $J$ to $1$ and then setting coordinate $i$ to $1$ ($\texttt{FABL.bribeFunction_insert}$). For any real-valued function, fixing coordinate $i$ to $1$ changes its mean by its Fourier coefficient at the singleton $\{i\}$ ($\texttt{FABL.mean_fixCoordinate_one}$). The already-bribed function remains monotone ($\texttt{FABL.monotone_bribeFunction}$), so its influence at $i$ equals that Fourier coefficient ($\texttt{FABL.influence_eq_fourierCoeff_singleton_of_monotone}$). The influence of the sign-valued function agrees with the influence of its real representation ($\texttt{FABL.booleanInfluence_eq_influence_toReal}$). Substituting these identities yields the claimed sum.

**Key facts.** `FABL.bribeFunction_insert`, `FABL.mean_fixCoordinate_one`, `FABL.monotone_bribeFunction`, `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.booleanInfluence_eq_influence_toReal`.
