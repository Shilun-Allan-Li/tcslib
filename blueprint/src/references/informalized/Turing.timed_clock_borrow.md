<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow pass over the clock word

**Claim.** Starting with borrow control, clock word $b_s$, and head at $0$, after $|b_s|$ steps the interpreter has traversed the word and reached the borrow control with the fixed-width subtraction result and head at $|b_s|$.

**Proof.** Apply the general borrow-pass run result (`timed_borrow_run`) with the starting frontier at $0$, no processed cells, and no unprocessed suffix beyond $b_s$. Its endpoint has frontier $|b_s|$, processed stack equal to the reversed optional-symbol encoding of the result word, and empty remainder. The starting zipper represents the buffer tape by `timed_buffer_zipper`. At the endpoint, `timedBorrow_length` says the result word has the same length as $b_s$, and `timed_buffer_zipper_end` identifies its buffer tape with precisely the endpoint zipper. Rewriting the start and end configurations by these identities gives the asserted run.

**Key facts.** `Turing.timed_borrow_run`, `Turing.timed_buffer_zipper`, `Turing.timedBorrow_length`, `Turing.timed_buffer_zipper_end`.
