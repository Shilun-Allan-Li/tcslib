<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_iff_polyTimeComputable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Indicator Characterization

**Claim.** A language $V$ belongs to $\mathsf{P}$ exactly when its one-bit indicator function is polynomial-time computable.

**Proof.** Unpack the characterization of membership in $\mathsf{P}$ (`Complexity.mem_P_iff`). In the forward direction, it supplies a machine and natural-number constants witnessing that the machine decides $V$ within a polynomial bound. By the definition of deciding in time, that machine outputs the one-bit indicator of $V$, so the same data witness polynomial-time computability of the indicator function. Conversely, a machine computing that indicator within a polynomial bound decides $V$ in the same time; applying the reverse direction of `Complexity.mem_P_iff` gives $V\in\mathsf{P}$.

**Key facts.** `Complexity.mem_P_iff`.
