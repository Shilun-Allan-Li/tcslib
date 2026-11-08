<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.booleanInfluence_tribes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a Tribes Coordinate

**Claim.** For positive tribe width $w$ and positive number of tribes $s$, every coordinate of the tribes function has influence $((2)^{w-1})^{-1}(1-2^{-w})^{s-1}$.

**Proof.** Fix the coordinate and let its tribe and its position within that tribe be the distinguished ones. By the pivotal-characterization lemma, the coordinate is pivotal precisely when all other positions in its own tribe are $-1$ and every other tribe evaluates to false (\texttt{FABL.isPivotal_tribes_iff}). Count these inputs by recording the distinguished coordinate's free sign and, for each other tribe, its block of signs. The latter block must make the AND function equal to $1$; there are $2^w-1$ such blocks (\texttt{FABL.card_andFunction_eq_one}). The coordinate reindexing lemma identifies the distinguished coordinate with its tribe-position pair (\texttt{FABL.finProdFinEquiv_tribesCoord}), so this data determines exactly one pivotal input and every pivotal input yields such data. There are therefore $2(2^w-1)^{s-1}$ pivotal inputs. Dividing by the total number $2^{sw}$ of cube inputs gives $2(2^w-1)^{s-1}/2^{sw}$. Rewriting this quotient by factoring $2^w$ from each of the $s-1$ other-block factors and using $2^w=2\cdot2^{w-1}$ yields the stated expression. This proof establishes the exact formula in the formal statement; it does not establish the additional asymptotic claims appearing in the supplied informal text.

**Key facts.** `FABL.isPivotal_tribes_iff`, `FABL.card_andFunction_eq_one`, `FABL.finProdFinEquiv_tribesCoord`.

**Caveat.** The provided informal statement includes asymptotic conclusions absent from the formal theorem and its proof. This account covers only the exact formula actually proved.
