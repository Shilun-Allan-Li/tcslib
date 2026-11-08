<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_recombine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BGW Circuit Reconstruction

**Claim.** Under the input-sharing hypothesis and $|A|\ge 2d+1$, recombining the shares produced by BGW evaluation of any circuit gives the ordinary circuit evaluation on the secret inputs.

**Proof.** By the sharing-preservation theorem (`bgwEval_isSharing`), the BGW output for the circuit is a degree-$d$ sharing of its ordinary value. The size hypothesis implies $d+1\le |A|$, so the reconstruction property for a sharing applies: recombining any such sharing over $A$ returns its secret (`IsSharing.recombine_eq`).

**Key facts.** `TCSlib.MPC.BGW.bgwEval_isSharing`, `TCSlib.Shamir.IsSharing.recombine_eq`.
