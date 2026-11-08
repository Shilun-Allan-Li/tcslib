<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5StoredRound_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computation of the Stored Round

**Claim.** For every finite Boolean-alphabet Turing machine $M$, the unary word whose length is its stored last-round index is polynomial-time computable.

**Proof.** First compute the stored header by composing the polynomial-time header-tail and header-field functions (\texttt{clHeaderTail\_native}, \texttt{clHeaderField\_native}, and polynomial-time closure under composition). From this header, extract the stored instance and fill a unary word of its length. Separately, extract the stored header tail used for the round count and fill a unary word of that length. The unary multiplication result (\texttt{clA5Times\_native}) scales this second word by $M$’s number of work tapes plus three. Concatenate the two unary words and the fixed unary word of length $M.k+1$ (\texttt{clA5\_pt\_const}, \texttt{clNative\_append}). Their total length is the stored last-round expression $n+(M.k+3)T+M.k+1$. Therefore this concatenation is exactly the desired unary output and is polynomial-time computable.

**Key facts.** `Complexity.clHeaderTail_native`, `Complexity.clHeaderField_native`, `Complexity.PolyTimeComputable.comp`, `Complexity.clNative_fill`, `Complexity.clA5Times_native`, `Complexity.clA5_pt_const`, `Complexity.clNative_append`.
