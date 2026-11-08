<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.PiP_three_subset_SigmaP_three_of_coNP_subset_NPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Third-Level Collapse from Circuits

**Claim.** Under the hypothesis that every language in coNP has the stated polynomial-size, fan-in-two circuit representation with polynomially many witness bits, every language in $\Pi_3^P$ belongs to $\Sigma_3^P$.

**Proof.** 1. Fix $L\in\Pi_3^P$. The level characterization supplies a language $L_2\in\Sigma_2^P$ and a polynomially bounded universal string $u$ such that $x\in L$ exactly when every allowed $u$ has the pair encoding of $x,u$ in $L_2$ (\texttt{mem\_PiP\_succ\_iff}). Unpacking the second-level Sigma characterization, there are a coNP language $K$ and polynomially bounded existential strings $v$ that witness membership of those encoded inputs in $L_2$ (\texttt{mem\_SigmaP\_two\_iff}).

2. Since $K\in\mathrm{coNP}$, it is in NP by the NP length characterization: membership can be certified by a polynomially bounded string $r$ and a polynomial-time language $R\in P$ (\texttt{mem\_NP\_iff\_exists\_length\_le}). The assumed hypothesis also gives a fan-in-two circuit family for $K$, with polynomially many extra input bits. A single polynomial bound is chosen to dominate the lengths of all encodings and witnesses used in these representations; the polynomial-bound closure facts justify combining and composing the bounds (\texttt{polyBound\_add}, \texttt{polyBound\_comp}, \texttt{polyBound\_smul}).

3. The proof packages the universal and existential checks into a new language whose membership asserts that the proposed circuit encoding has no locally detectable bad specification. Its membership in $\Pi_2^P$ follows from the established inner-language result (\texttt{innerLang\_mem\_PiP}). The soundness lemma shows that if such an encoding passes all checks, then the original second-level condition holds (\texttt{sound}). Conversely, the circuit family for $K$ supplies an encoding that passes every check whenever the original condition holds; this is the completeness direction (\texttt{complete}).

4. The resulting language therefore has existential witnesses of polynomially bounded length whose pair encodings lie in a $\Pi_2^P$ language. The next-Sigma-level criterion turns this into membership in $\Sigma_3^P$ (\texttt{mem\_SigmaP\_succ\_of\_exists\_le}). The circuit encoding length is bounded using the fan-in-two encoding estimate (\texttt{DAGCircuit.length\_encode\_le\_of\_isFaninTwo}); the chosen polynomial bound ensures it fits the required witness budget. This represents $L$ in $\Sigma_3^P$, proving the claim.

**Key facts.** `Complexity.mem_PiP_succ_iff`, `Complexity.mem_SigmaP_two_iff`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.Yap.polyBound_add`, `Complexity.Yap.polyBound_comp`, `Complexity.Yap.polyBound_smul`, `Complexity.Yap.innerLang_mem_PiP`, `Complexity.Yap.sound`, `Complexity.Yap.complete`, `Complexity.Yap.mem_SigmaP_succ_of_exists_le`, `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`.

**Caveat.** The proof delegates the detailed construction and correctness of the encoded local checks to the stated soundness and completeness lemmas; their full definitions are not included in the supplied upstream statements.
