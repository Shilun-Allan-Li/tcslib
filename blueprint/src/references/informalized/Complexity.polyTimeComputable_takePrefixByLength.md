<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.polyTimeComputable_takePrefixByLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length-Bounded Prefix

**Claim.** For a bit string $z$, parse its two components using the aligned pair parser, taking both to be empty if parsing fails. The function that returns the prefix of the second component whose length is the length of the first component is polynomial-time computable.

**Proof.** The proof uses the counter program for this prefix operation, with its scan label as the initial label and parameters $C=5$ and $c=1$. For each input $z$, the program’s totality result supplies a run that halts with output equal to the requested prefix, and whose time is $5(|z|+1)$. This is a polynomial bound of the form required by the general theorem turning a program with such bounded halting runs into a polynomial-time computable function. Hence the prefix function is polynomial-time computable (`polyTimeComputable_of_goes`, using `goes_total`).

**Key facts.** `Complexity.CounterProg.polyTimeComputable_of_goes`, `Complexity.PrefixByLength.goes_total`.
