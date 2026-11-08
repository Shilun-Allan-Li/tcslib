<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_compile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Compilation of an Exponential Certificate Language

**Claim.** Under the certificate condition for $L$ and the polynomial-time decision bound for $V$, a finite nondeterministic machine decides $L$ within a bound of the stated form.

**Proof.** First use the exponential scheduler to obtain a finite machine that produces, on input of length $n$, a unary word of length $C(2^{n+1})^c$, within the stated polynomial bound. The unary-input simulation result (b2_unary_first) turns this into a run on the actual input $x$ with a time $[4m[0m\tau(|x|)$ no larger than that bound and with no earlier halt. Run the host machine that combines this scheduler with the decider for $V$. Its contract (b2_host_contract) gives a fixed total number $H$ of nondeterministic steps: every choice sequence of that length halts, and its output is the indicator of whether the concatenation of $x$ with the guessed certificate belongs to $V$. Conversely, any certificate of the prescribed length accepted by $V$ yields a choice sequence with output true; and any such choice sequence with output true yields a certificate of that length in $V$. The certificate equivalence therefore identifies the host's accepting choice sequences exactly with membership in $L$. Finally, the scheduler's time bound and the host time estimate give $H\le (B+A+5)(n+C2^{(n+1)^c}+1)^{c+2+d+1}$. Halting within $H$ implies halting within this larger bound (HaltsWithin.mono), and once all runs halt, acceptance is unchanged by extending the choice sequence (acceptsWithin_iff_of_halts). Thus the host machine decides $L$ with the claimed constants.

**Key facts.** `Complexity.a2_exp_scheduler`, `Complexity.b2_unary_first`, `Complexity.b2_host_contract`, `Complexity.a2_host_bound`, `Turing.NDTM.HaltsWithin.mono`, `Complexity.acceptsWithin_iff_of_halts`.

**Caveat.** The supplied upstream statement for b2_host_contract is truncated, so the exact converse clause is inferred from the proof’s use of hc.2 and its displayed arguments.
