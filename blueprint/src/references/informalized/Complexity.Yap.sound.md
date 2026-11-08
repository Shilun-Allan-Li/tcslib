<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Soundness of the Inner-Language Condition

**Claim.** Under the stated witness and refutation characterizations and length bound, if $\langle x,U\rangle$ belongs to the inner language and $|u|=M_1(x)$, then $\langle x,u\rangle\in L_2$.

**Proof.** Membership of $\langle x,U\rangle$ in the inner language says that, for every string $t$, the pairing of $\langle x,U\rangle$ with $t$ is not in the bad language (`Complexity.Yap.Data.mem_innerLang`). By the characterization of the bad language and the simplification of checking a paired input (`Complexity.Yap.Data.mem_badLang`, `Complexity.Yap.Data.check_pair`), each $t$ within the allowed bound therefore has some $e$ for which the core condition fails.

First choose $t=\langle\langle u,\epsilon\rangle,\langle\epsilon,\epsilon\rangle\rangle$, where $\epsilon$ is the empty string. The assumed length bound puts this $t$ within range. Its decoded components reduce to the displayed strings because pairing decodes to its components (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). Since $|u|=M_1(x)$, failure of the core condition forces an $e$ whose first decoded component supplies a string $v$ of length $M_2(\langle x,u\rangle)$ and for which the query on $U$ with input $\langle\langle x,u\rangle,v\rangle$ followed by the second decoded component of $e$ holds. In particular, $\langle x,u\rangle$ has the required length-$M_2$ witness; it remains to show its paired encoding with $v$ lies in $K$.

Suppose instead that this paired encoding is not in $K$. The refutation characterization gives a string $r$ of length at most $C_3(|\langle\langle x,u\rangle,v\rangle|+1)^{c_3}$ whose pairing with $\langle\langle x,u\rangle,v\rangle$ lies in $R$. The exact length identity for such paired inputs (`Complexity.Yap.Data.length_inst`) identifies the inner length with $nLen(x)$, so this $r$ meets the required bound. Also, the query length bound (`Complexity.Yap.length_le_of_query`) says the second decoded component of $e$ has length at most $|U|$. The assumed global bound now puts $t'=\langle\langle u,v\rangle,\langle w,r\rangle\rangle$ within the allowed range, where $w$ is that second component. Apply the inner-language consequence again to obtain an $e_1$ for which the core condition at $t'$ fails. With the decoded components and $|u|=M_1(x)$ substituted, this failure rules out the alternative that the proposed matched query fails, since that query is the one already obtained from $e$. It must therefore be the other alternative: the strings $v,w,r$ satisfy the sound-failure conditions, including the query and the refutation in $R$. This contradicts the failure of the core condition at $t'$. Hence the paired encoding with $v$ belongs to $K$.

The characterization of $L_2$ now applies: the string $v$ has exactly the required length and its pairing with $\langle x,u\rangle$ is in $K$. Thus $\langle x,u\rangle\in L_2$.

**Key facts.** `Complexity.Yap.Data.mem_innerLang`, `Complexity.Yap.Data.mem_badLang`, `Complexity.Yap.Data.check_pair`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.Yap.Data.length_inst`, `Complexity.Yap.length_le_of_query`.

**Caveat.** The supplied informal statement describes the final claim, but the Lean proof uses the definitions of the core condition, match, and sound-failure relation to derive the intermediate alternatives. The account follows those definitions as included in the formal statement; the stated universal-machine fact is not used by this proof.
