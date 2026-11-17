<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InRP.inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# RP is contained in BPP

**Claim.** An efficient randomized verifier with acceptance probability at least $2/3$ on members and zero acceptance probability on nonmembers gives a BPP verifier with both correctness probabilities at least $2/3$.

**Proof.** Unpack the RP verifier and keep its machine and random-bit bound. On members, its existing acceptance guarantee is exactly the BPP requirement. On a nonmember, every random string makes the machine reject. Thus the event of rejection holds for every random string, so its probability equals the probability of the certain event, namely $1$ (Randomized.randProb_congr and Randomized.randProb_true). Since $2/3\le 1$, the required rejection bound follows.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_true`.
