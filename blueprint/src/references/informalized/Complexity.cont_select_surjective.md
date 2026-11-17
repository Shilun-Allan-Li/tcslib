<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_select_surjective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Surjectivity of Word Selection

**Claim.** If $u$ has length equal to the number of true entries in $mask$, then some word $w$ of length $|mask|$ selects to exactly $u$ along $mask$.

**Proof.** Induct on $mask$, generalizing over $u$. For empty $mask$, the length condition forces $u$ to be empty, and the empty word is a preimage. For $mask= false::mask'$, the length condition reduces to the same condition for $mask'$ and $u$. By induction choose a preimage $w'$ of length $|mask'|$; prefixing any bit, say false, gives a word of length $|mask|$, and the leading false mask entry discards that bit, leaving the selection of $w'$. For $mask=true::mask'$, the length condition implies $u$ is nonempty; write $u=b::u'$. The tail $u'$ has the number of true entries in $mask'$, so induction supplies a preimage $w'$ for it. Prefix $b$ to $w'$. The leading true entry selects $b$, followed by the selection of $w'$, yielding exactly $u$.
