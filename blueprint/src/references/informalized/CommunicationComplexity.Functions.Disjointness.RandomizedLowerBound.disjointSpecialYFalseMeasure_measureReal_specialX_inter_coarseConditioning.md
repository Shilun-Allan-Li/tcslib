<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity on Coarse Fibers

**Claim.** Under the distribution conditioned on disjointness and on Bob’s special bit being false, Alice’s special bit is uniform on each fiber of the coarse variable: for each bit $b$ and coarse value $c$, the mass where both $X_T=b$ and the coarse variable equals $c$ is half the mass of that coarse fiber.

**Proof.** Fix a bit $b$ and a coarse value $c$. Write $Y_0$ for the event that Bob’s special bit is false, $X_b$ for the event that Alice’s special bit equals $b$, and $C$ for the event that the coarse variable equals $c$. By the conditional-measure formula, each of the two desired masses under the final conditioning is the corresponding mass under the disjointness-conditioned law, intersected with $Y_0$, divided by the common normalizing mass of $Y_0$. It remains to establish the half-mass identity before that final conditioning. Under the ambient uniform law, the event $Y_0\cap C\cap X_b$ has half the mass of $Y_0\cap C$ (\texttt{volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX}). Both of these events imply disjointness because Bob’s bit at the special coordinate is false (\texttt{mem_disjointEvent_of_specialY_eq_false}). Thus conditioning on disjointness multiplies both masses by the same normalizing factor, preserving their ratio of one half. Substituting this identity into the two conditional-measure formulas cancels their shared normalization and gives the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_disjointEvent_of_specialY_eq_false`.
