<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Convention.lean :: Turing.incFixed_replicate_true_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing a True Prefix

**Claim.** For every natural number $n$ and Boolean word $w$, incrementing $n$ true bits followed by $w$ gives the increment of $w$ with $n$ false bits prefixed, with both results undefined when incrementing $w$ overflows.

**Proof.** Induct on $n$. When $n=0$, the prefix is empty, so the assertion is the identity. For the successor step, write the longer prefix as one true bit followed by the prefix of length $n$. By the induction hypothesis, incrementing the latter prefix and $w$ either remains undefined, or produces $n$ false bits followed by the incremented word. The increment rule on the additional leading true bit changes that bit to false and maps the same prefixing operation over the result. Thus the result has $n+1$ false bits prefixed, and the undefined case is preserved.
