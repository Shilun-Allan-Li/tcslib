<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.getElem?_dbl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a Doubled Word

**Claim.** If $c<|w|$ and $p$ is Boolean, the doubled word has value $w_c$ at position $2c+p$, where $p$ is read as $0$ or $1$.

**Proof.** Induct on the word. For the empty word the index hypothesis is impossible. For a nonempty word, if $c=0$, the first two entries of the doubled word are both the head bit, so either Boolean choice of $p$ selects that bit. If $c$ is a successor, the doubled word consists of two copies of the head bit followed by the doubled tail. The desired index is therefore two positions past the corresponding index in that tail: the identity $2(c+1)+p= (2c+p)+2$ aligns the indices. The induction hypothesis gives the tail entry, and the list-index calculation yields the result. The decomposition of the doubled cons word is the fact `dbl_cons`.

**Key facts.** `Turing.dbl_cons`.
