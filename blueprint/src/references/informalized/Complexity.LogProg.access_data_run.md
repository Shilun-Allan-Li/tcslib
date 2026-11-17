<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_data_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Data Bit

**Claim.** On the self-delimiting pair encoding of $z$ and $w$, the access machine reads the bit of $z$ at index $k$ when it exists, and follows the stated answer or bump branch, ending with the pointer and tapes advanced as specified.

**Proof.** The pair encoding consists of the doubled word for $z$, followed by the separator and then $w$ (`pairEncode_eq_dbl`). At positions $2k$ and $2k+1$, it therefore contains two copies of $z_k$ if $k<|z|$; when $k=|z|$, these positions contain the two separator bits, false and true. This indexing follows from the doubled-word lookup and length formulas (`getElem?_dbl`, `length_dbl`, `length_pairEncode`). The access-read result (`access_read`) reads the bit at position $2k$ and stores it in the state; a state jump (`access_jump`) then begins the second read. Incrementing the data pointer by one via `access_inc_pointer` moves its position from $2k$ to $2k+1$, after which `access_read` reads the second bit. If the first position was an actual data bit, the two copies agree, and the machine takes the answer branch with value $m\lor z_k$ when $e$ is true, or the bump branch when $e$ is false. At the end of $z$, the separator bits differ, so the machine answers false. The final jump leaves the pointer at $2k+1$ and gives exactly the asserted state; the intermediate reads and pointer movement preserve the required head bounds.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Turing.getElem?_dbl`, `Turing.length_dbl`, `Turing.length_pairEncode`, `Complexity.LogProg.access_read`, `Complexity.LogProg.access_jump`, `Complexity.LogProg.access_inc_pointer`.
