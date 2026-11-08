<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Phase Over a Clock Word

**Claim.** For a Boolean word $x$, a base configuration of the timed interpreter on input $x$, action bits, flags $h,r$, a Boolean word $b_s$, integer frontier $z$, and finite lists $l,r_s$ of possibly blank bits, running the interpreter for $|b_s|$ steps from the borrow phase with flag $r$ and zipper state $(z,l,b_s\mathbin{+}r_s)$ yields the borrow phase with the final borrow from subtracting $r$ from $b_s$, frontier $z+|b_s|$, processed stack the reversed resulting word followed by $l$, and unprocessed list $r_s$.

**Proof.** Apply the general lane-sweep result to lane $4$, with the borrow control as its state, each Boolean as its tape symbol, and the local update $(c,b)\mapsto(c\land\neg b,\,b\mathbin{\mathrm{xor}}c)$. The transition of the timed interpreter on this lane performs exactly that update whenever the current tape cell contains the corresponding bit (`Turing.timedAdmin_clock`). The lane-sweep result therefore describes the configuration after one step for each bit: the frontier advances by the word length, the updated bits form the processed portion in reverse order followed by the prior stack, and the untouched suffix remains $r_s$ (`Turing.timed_lane_run`). Finally, the fold of these local updates is exactly the recursively defined borrow computation (`Turing.timedBorrow_fold`), giving the stated final carry and word.

**Key facts.** `Turing.timedAdmin_clock`, `Turing.timed_lane_run`, `Turing.timedBorrow_fold`.
