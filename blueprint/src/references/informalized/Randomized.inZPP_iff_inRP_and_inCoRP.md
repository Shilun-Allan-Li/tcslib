<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.inZPP_iff_inRP_and_inCoRP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-error randomized characterization

**Claim.** Under the stated closure properties, a language has a zero-error verifier with abort probability at most $1/2$ exactly when both the language and its complement have one-sided randomized verifiers with acceptance probability at least $2/3$.

**Proof.** Given a zero-error verifier for $L$, apply the zero-error-to-one-sided conversion (`Randomized.inRP_of_zeroError`) with target answer true to obtain an RP verifier for $L$. The zero-error conditions ensure it never answers false on members and never answers true on nonmembers, while its abort probability is at most $1/2$. Apply the same conversion to the complement, targeting false: members of the complement are precisely nonmembers of $L$, so the same conditions give the required one-sided verifier for $L^c$.

In the other direction, let $M_1$ be the RP verifier for $L$ and $M_2$ the RP verifier for $L^c$. First trim $M_2$'s random tape to its prescribed polynomial length: the closure under polynomially many OR trials with one trial reproduces exactly this single-block test. Race $M_1$ on the first block against the trimmed $M_2$ on the second, returning true if the first accepts, false if the second accepts, and otherwise aborting. The race closure gives efficiency. The sum of the two polynomial block lengths is bounded by a polynomial of the form used for the new verifier; each extracted block has its required length and can be represented by a random tape of that length (`Randomized.exists_ofFn_eq`).

On a member of $L$, the second verifier never accepts, so the race cannot answer false; on a nonmember, the first verifier never accepts, so it cannot answer true. The abort event is exactly the event that both block tests reject. Independence of the blocks makes its probability the product of their rejection probabilities (`Randomized.randProb_split`, with the second block's unused suffix removed using `Randomized.randProb_take`). On a member, the first verifier accepts with probability at least $2/3$, so its rejection probability is at most $1/3$; on a nonmember, the second has that bound. The other factor is at most $1$. Thus the abort probability is at most $1/3$, hence at most $1/2$, as required.

**Key facts.** `Randomized.inRP_of_zeroError`, `Randomized.exists_ofFn_eq`, `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_take`, `Randomized.randProb_not`, `Randomized.randProb_le_one`, `Randomized.randProb_nonneg`.
