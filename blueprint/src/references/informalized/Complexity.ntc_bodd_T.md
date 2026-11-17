<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_bodd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity of the Modified Time Bound

**Claim.** The parity of the modified time bound $T(n)$ equals the parity of $n$ exclusive-or the halting predicate evaluated on the specified string.

**Proof.** Expand the definition of $T(n)$. If the halting predicate is false, then $T(n)=n$, and exclusive-or with false leaves the parity of $n$ unchanged. If the predicate is true, then $T(n)=n+1$, whose parity is the opposite of the parity of $n$; exclusive-or with true also reverses that parity. In both cases the claimed identity follows.
