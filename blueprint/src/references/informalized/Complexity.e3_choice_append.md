<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_choice_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership for a correctly sized choice word

**Claim.** For a finite nondeterministic Turing machine $N$ over the binary alphabet, natural numbers $C,c$, and binary strings $x,u$ with $|u|=C\cdot2^{(|x|+1)^c}$, the concatenation $xu$ belongs to the choice-word verifier language exactly when running $N$ on $x$ with choice word $u$ halts with output exactly $1$.

**Proof.** By definition, membership provides strings $y,v$ such that $v$ has the prescribed length for $y$, $x\mathbin{+}u=y\mathbin{+}v$, and the run on $y$ using $v$ halts with output $1$. The uniqueness-of-split fact says that when the total length is of the form $n+f(n)$ for a strictly increasing function $n\mapsto n+f(n)$, two such decompositions must have identical prefixes and suffixes (\texttt{Turing.append_split_unique}). Here $f(n)=C\cdot2^{(n+1)^c}$, and its required strict increase is supplied by \texttt{Turing.expCertificateLength_strictMono}. Thus $y=x$ and $v=u$, leaving precisely the claimed halting and output conditions. Conversely, if those conditions hold, choosing $x,u$ themselves as the verifier's witness strings proves membership directly.

**Key facts.** `Turing.append_split_unique`, `Turing.expCertificateLength_strictMono`.
