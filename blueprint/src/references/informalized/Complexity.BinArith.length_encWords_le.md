<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_encWords_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Encoded List Length

**Claim.** If every word in $L$ has length at most $c$, then the concatenated encoding has length at most $|L|(2c+2)$.

**Proof.** Induct on $L$. The empty list has encoding length zero. For a list with head $w$ and tail $L'$, the encoding is the pair encoding of $w$ with the encoding of $L'$ (`Complexity.BinArith.encWords_cons`). Its length is $2|w|+2$ plus the tail encoding length (`Turing.length_pairEncode`). The hypothesis bounds $|w|$ by $c$, and the induction hypothesis applies to the tail because every word occurring there also occurs in $L$. Adding the head bound to the tail bound gives $(2c+2)+|L'|(2c+2)=|L|(2c+2)$.

**Key facts.** `Complexity.BinArith.encWords_cons`, `Turing.length_pairEncode`.
