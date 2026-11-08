<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.eval_toF₂Real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under binary sign encoding

**Claim.** For a finite decision tree whose inputs and outputs are signs, the associated binary decision tree evaluated at a binary vector gives the real value of the original tree evaluated at its coordinatewise sign encoding.

**Proof.** Proceed by induction on the tree. At a leaf, both sides give the real value of the stored sign. At a query of coordinate $i$, the binary tree tests whether $x_i=0$. If so, the sign encoding of that bit is $1$, and the converted tree selects the child labelled by $1$. The induction hypothesis for that child gives the desired equality. If $x_i\ne0$, its sign encoding must be $-1$: it is a sign, and if it were $1$, injectivity of the binary-to-sign encoding would force $x_i=0$. The converted tree therefore selects the child labelled by $-1$, and that child's induction hypothesis completes the argument. The coordinatewise encoding used here is the one characterized by $(\mathrm{binaryCubeSignEquiv}\ n\ x)_i=\mathrm{signEncode}(x_i)$ (\texttt{FABL.binaryCubeSignEquiv\_apply}); in the zero case, $\mathrm{signEncode}(0)=1$ (\texttt{FABL.signEncode\_zero}).

**Key facts.** `FABL.binaryCubeSignEquiv_apply`, `FABL.signEncode_zero`.
