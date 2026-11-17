<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterOverhead_le_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overhead bound for an initial segment

**Claim.** For every Boolean word $w$ and every $r\le V(w)$, the overhead accumulated over the first $r$ rounds is at most $4r+2|w|$.

**Proof.** The counter-potential identity gives $\operatorname{overhead}(w,r)+2\,\#_1(w)=4r+2\,\#_1(\operatorname{counterWord}(w,r))$. The number of true bits in the counter word is at most its length, and `counterWord_length` says that this length is $|w|$. Dropping the nonnegative term $2\,\#_1(w)$ from the left-hand side yields the desired bound.

**Key facts.** `Turing.counter_potential`, `Turing.counterWord_length`.
