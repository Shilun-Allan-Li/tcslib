<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding in the Inner Language

**Claim.** Under the stated certificate, refutation, circuit, and length-bound hypotheses, if every string $u$ of length $M_1(x)$ satisfies $\langle x,u\rangle\in L_2$, then the pairing of $x$ with the encoding of the specified circuit belongs to the inner language.

**Proof.** Fix an arbitrary string $t$. The inner-language criterion reduces the goal to showing that pairing $t$ with the proposed string is not in the bad language. By the bad-language membership criterion, it is enough to find a test string within the prescribed length bound for which the check fails. Simplifying the decoded components of the pairing and the check condition, the relevant first input is the circuit encoding $U=D_{nLen(x)}.encode$, and the candidate certificate block is $u$, the first projection of the first projection of $t$.

First suppose $|u|=M_1(x)$. The assumption on $L_2$ supplies a string $v$ of length $M_2(\langle x,u\rangle)$ such that $\langle\langle x,u\rangle,v\rangle\in K$. The length-instantiation fact (`length_inst`) identifies the length of this paired input with $nLen(x)$. The certificate characterization of $K$ by the circuit then gives an accepting assignment $y$ for the last input bits of the circuit on this input.

Use $e=\langle v,\mathrm{ofFn}(y)\rangle$ as the test string. This test is within the bound required by the bad-language condition: the assumed bound `hB` applies because the certificate length has the required polynomial estimate, and the assignment list has length at most the circuit encoding length. For that last estimate, the circuit size is at most its encoding length (`size_le_length_encode`), and the equality of the input length with $nLen(x)$ aligns the relevant circuit sizes.

Now inspect the disjunction in the check condition. If its sound-failure alternative held, its claimed membership in the refutation relation would, by the refutation characterization `hK`, imply that the corresponding circuit query input is outside $K$. But the query says that this input is accepted by the encoded circuit: `query_append_iff` converts the query into an accepting assignment, and its input-length premise follows from `length_inst`. This contradicts membership in $K$. If instead the other alternative held, it would deny the match witnessed by $v$ and the accepting assignment $y$; the same query characterization and the certificate facts give precisely that match. Thus the check fails for this test string.

Finally, if $|u|\ne M_1(x)$, take the empty test string. Its length meets the bound, and the first conjunct of the core check requires $|u|=M_1(x)$, so the check fails immediately. In either case a permitted test violates the bad-language condition. Since $t$ was arbitrary, every such pairing is outside the bad language, proving membership in the inner language.

**Key facts.** `Complexity.Yap.Data.mem_innerLang`, `Complexity.Yap.Data.mem_badLang`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.Yap.query_append_iff`, `Complexity.Yap.Data.length_inst`, `Complexity.Yap.Data.check_pair`, `BoolCircuit.DAGCircuit.size_le_length_encode`, `Turing.length_pairEncode`.
