<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_isSharing -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BGW Evaluation Preserves Sharings

**Claim.** If every input wire is supplied with a degree-$d$ sharing of its value and $|A|\ge 2d+1$, then every circuit's BGW evaluation is a degree-$d$ sharing of its ordinary value.

**Proof.** Proceed by structural induction on the circuit. For an input wire, the claim is the assumed input-sharing property; for a public constant, it is the fact that a constant polynomial gives a sharing of that constant (`isSharing_const`). At an addition gate, the two inductive sharing statements combine by closure of sharings under addition (`IsSharing.add`). At a public-scalar gate, closure under scalar multiplication gives the result (`IsSharing.smul`). At a multiplication gate, the two degree-$d$ sharings yield a degree-$(d+d)=2d$ sharing of the product, by the product rule for sharings (`IsSharing.mul`). The degree-reduction theorem then turns this into a degree-$d$ sharing of the same product, using $|A|\ge 2d+1$ (`isSharing_degreeReduce`).

**Key facts.** `TCSlib.Shamir.isSharing_const`, `TCSlib.Shamir.IsSharing.add`, `TCSlib.Shamir.IsSharing.smul`, `TCSlib.Shamir.IsSharing.mul`, `TCSlib.MPC.BGW.isSharing_degreeReduce`.
