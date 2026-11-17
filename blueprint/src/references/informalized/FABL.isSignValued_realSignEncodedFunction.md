<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isSignValued_realSignEncodedFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Sign Encoding Is Sign-Valued

**Claim.** Encoding the values of a Boolean function as real signs produces a function whose absolute value is $1$ at every input.

**Proof.** Fix an input. Its encoded value is a sign, and every sign has real value either $-1$ or $1$ (\(\texttt{signValue\_eq\_neg\_one\_or\_one}\)). In either case the absolute value is $1$, proving the assertion pointwise.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
