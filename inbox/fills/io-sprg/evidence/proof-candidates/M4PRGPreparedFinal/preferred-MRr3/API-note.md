# Helper04 — binding MRr3 public-reader repair (UNRUN)

Preferred body:04-prg_verdict_prob.proposed.lean. It differs from the previous
prepared helper by exactly one rewrite line; the complete header/docstring,
actual coin reindexing and uniform-prefix probability transport remain unchanged.
Other package proof files are untouched. This candidate has one outer tactic
block and has not been run in Lean or applied to implementation source.

After reindexing B.Coins N through coinsEquivPoly, the local r is already a
bit vector of length (A.coins.subst .var).eval N. The required specific reader is
Complexity.NUPPT.RealizesOn.runAt_coinsEquivPoly_symm, defined at
TCSlib/Cryptography/Asymptotic/Realization.lean:141. With hB, it reads the activation
on the inverse-equivalence coins directly as the advised reduction on List.ofFn r.

The preferred composition is:
1. Complexity.NUPPT.distinguisherL_eq (Adversary.lean:386) exposes the ordinary
   machine verdict as decide(runAt = [true]). This is the generic machine reader,
   not a second invocation of the shared realizer verdict theorem.
2. hB.runAt_coinsEquivPoly_symm consumes exactly the reindexed bit-vector shape.
   Together with the first reader it gives the required bit-vector verdict.
3. P.prgRed_eq reads the owned reduction and its actual A coin prefix.

The previous hB.distinguisherL_eq + coinsEquivPoly_symm_ofFn sequence inlined the
more-specific second reader. It is superseded here. No meaningless extra use of
RealizesOn.distinguisherL_eq is added merely to cite another shared API: that
reader handles the unreindexed B.Coins form and is unnecessary in this branch.

Actual distributional work remains intact:uprob_comp_equiv carries B's uniform
coins through the supplied equivalence; the existing pushesUniform_restrict law
then restricts to A.coinLen(kappaOfN N), justified by the same hcut; the existing
ofFn_castLE_eq_take equation transports that restriction to the actual list prefix.
These probability transports are still required and are not replaced by a
pointwise verdict equality.

The original endpoint, statistical-hop and hop candidates and all other helper bodies
are unchanged. Params.sdCore_publicSeed belongs in Hybrids beside publicSeed,
before the statistical hops; helper04 and the other PRG reduction helpers belong
in Reductions/PRG/Hop. This note creates no source declaration or placement change.
