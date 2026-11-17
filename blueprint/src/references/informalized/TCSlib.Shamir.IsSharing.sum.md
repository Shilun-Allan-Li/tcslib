<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.IsSharing.sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of sharings

**Claim.** For a finite set of indices, if each corresponding function shares its value with degree bound $d$, then the pointwise sum of those functions shares the sum of the values with the same degree bound.

**Proof.** Induct on the finite index set. For the empty set, the sum of values and the pointwise sum of shares are both zero, and the constant-zero sharing supplies the result (`TCSlib.Shamir.isSharing_const`). For the inductive step, write the set as an inserted index $a$ and the remaining set $s$. By the induction hypothesis, the shares indexed by $s$ share the sum of their values. The sharing at $a$ and this sharing of the remainder can be added: sums of sharings with the same degree bound remain sharings with that bound (`TCSlib.Shamir.IsSharing.add`). The finite-sum identities identify this sharing with the sum over the inserted set, both for the secret values and party by party for the shares.

**Key facts.** `TCSlib.Shamir.isSharing_const`, `TCSlib.Shamir.IsSharing.add`.
