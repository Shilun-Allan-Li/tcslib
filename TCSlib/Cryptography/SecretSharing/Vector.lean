/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Sharing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharing a vector of secrets

A protocol never shares one field element; it shares one per input wire, each with independent
coins. This file packages that as a scheme in its own right, `Shamir.vecScheme`, and shows that
correctness and perfect privacy lift coordinatewise. The privacy statement is the one that
matters for protocols: the joint view of an unauthorized set across *all* the sharings is
independent of *all* the secrets simultaneously, not merely one at a time.

## Main definitions

* `TCSlib.Shamir.vecScheme`: Shamir sharing of an `ι`-indexed vector of secrets.

## Main results

* `TCSlib.Shamir.vecScheme_correct`, `TCSlib.Shamir.vecScheme_perfectPrivacy`.
* `TCSlib.Shamir.isSharing_vecScheme`: each coordinate of the dealt vector is a sharing.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017, §3.2.
-/

namespace TCSlib.Shamir

open Finset Polynomial TCSlib.SecretSharing

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} {k : ℕ}

/-- Shamir sharing of a vector of secrets, one independent sharing per coordinate: party `i`
receives the vector of its shares. [AL17, §3.2] -/
noncomputable def vecScheme (k : ℕ) (F : Type*) [Field F] [DecidableEq F] (ι : Type*) :
    Scheme (Party F) (ι → F) (ι → F) (ι → degreeLT F (k - 1)) where
  share v q i := fun x => (scheme k F).share (v x) (q x) i
  reconstruct A f := fun x => (scheme k F).reconstruct A (fun i => f i x)

/-- Each coordinate of a dealt vector is a degree-`(k-1)` sharing of the corresponding secret;
this is the hypothesis the BGW correctness theorem takes on its inputs. -/
theorem isSharing_vecScheme (hk : 0 < k) (v : ι → F) (q : ι → degreeLT F (k - 1)) (x : ι) :
    IsSharing (k - 1) (v x) (fun i => (vecScheme k F ι).share v q i x) :=
  isSharing_share hk (v x) (q x)

/-- **Correctness.** Any `k` parties reconstruct the whole vector. -/
theorem vecScheme_correct (hk : 0 < k) :
    (vecScheme k F ι).Correct (AccessStructure.threshold k) := by
  intro A hA v q
  funext x
  exact correct hk A hA (v x) (q x)

/-- **Perfect privacy, jointly in all coordinates.** For any set of at most `k - 1` parties and
any two secret vectors there is a bijection of the coin vectors carrying the one's joint view to
the other's: the shares of `k - 1` parties are independent of the entire secret vector.

**Proof sketch.** Apply single-secret privacy in each coordinate to get a bijection `eₓ` of that
coordinate's coins, and take the product bijection `∏ₓ eₓ` of the coin vectors; since the coins
of distinct coordinates are independent, this is a bijection of the whole coin space, and it
fixes the view coordinatewise by construction. -/
theorem vecScheme_perfectPrivacy :
    (vecScheme k F ι).PerfectPrivacy (AccessStructure.threshold k) := by
  intro B hB v v'
  choose e he using fun x : ι => perfectPrivacy (F := F) (k := k) B hB (v x) (v' x)
  refine ⟨Equiv.piCongrRight e, fun q i hi => ?_⟩
  funext x
  exact he x (q x) i hi

end TCSlib.Shamir
