/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.ComposeSecurity
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Theorem 163.7 for the real protocol (statement phase)

[PS10, Protocol 162.6 and Theorem 163.7]: Yao's protocol, with Bob's keys transferred by the
oblivious transfer of Protocol 160.4, securely computes the circuit's function against
honest-but-curious parties.

**How it is obtained** (ruling of 2026-11-05, Q-5 option 1). The real protocol is the
composition (`HybridProtocol.compose`) of Yao in the OT-hybrid model (`yaoHybrid`) with
Protocol 160.4, one run per transferred key bit (`inB(n) · n` runs). Its security is a corollary
of three theorems:
- Theorem 163.7 in the OT-hybrid model (`yaoHybrid_hbcSecure`);
- Proposition 161.5 (`otProtocol_hbcSecure`);
- the composition theorem of [Gol04, Theorem 7.3.3] (`HybridProtocol.hbcSecure_compose`), whose
  side condition holds because Yao's message phase has two moves.

The hypotheses are theirs: the PRFs of the garbling, the circuit family (in `YaoCircuit`), and
the trapdoor collection with its hard-core predicate for the oblivious transfer.

**Source note.** The source runs "a 1-out-of-2 oblivious transfer" of each key pair and calls the
generalization of Protocol 160.4 to `n`-bit strings straightforward; here each key bit is
transferred by its own run of Protocol 160.4 (`yaoHybrid`'s calls).

## Main definitions

* `SecureComputation.yaoProtocol`: Protocol 162.6 with Protocol 160.4 for the transfers.

## Main results

* `SecureComputation.yaoProtocol_hbcSecure` (Theorem 163.7, proved from the three theorems
  above, and so resting on their `sorry`s).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4–6.2.5, Protocol 160.4, Proposition 161.5, Protocol 162.6 and Theorem 163.7
  (book pp. 160–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3.1, Theorem 7.3.3 (numbering to be verified at audit).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

variable (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (T : TrapdoorCollection)
  (H : List Bool → List Bool)

/-- **Protocol 162.6 with real oblivious transfers** [PS10]: Yao in the OT-hybrid model
(`yaoHybrid`), composed with Protocol 160.4 (`otProtocol`) for its `inB(n) · n` bit transfers
(`HybridProtocol.compose`). -/
noncomputable def yaoProtocol : Protocol := (yaoHybrid Y E₁ E₂).compose (otProtocol T H)

/-- **Theorem 163.7** [PS10]: Protocol 162.6, with Protocol 160.4 for the transfers, is an
honest-but-curious secure protocol for the circuit's function. The hypotheses are those of
Theorem 163.7 in the OT-hybrid model (the PRFs of the garbling, jointly as well) and of
Proposition 161.5 (a collection of trapdoor permutations with a hard-core predicate evaluated by
`H`).

**Proof sketch.** The composition theorem (`HybridProtocol.hbcSecure_compose`) applied to
`yaoHybrid_hbcSecure` and `otProtocol_hbcSecure`. Its side condition, that the message phase has
at least one move, holds since `yaoMain` has two. -/
theorem yaoProtocol_hbcSecure
    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x))
    (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₂ n s x))
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x)))
    {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (hspec : ∀ i w x, T.decD i w = some x → H (pairEncode i w) = [h i x])
    (hT : T.OneWay) (hHC : T.toCollection.HardCore h) (hcanon : SamplerCanonical T) :
    HBCSecure (yaoProtocol Y E₁ E₂ T H) (yaoFunctionality Y) :=
  (yaoHybrid Y E₁ E₂).hbcSecure_compose (otProtocol T H)
    (fun n => by show 0 < (PolyExpr.const 2).eval n; simp)
    (yaoHybrid_hbcSecure Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hE₁ hE₂ hG₁ hG₂ hG₁₂)
    (otProtocol_hbcSecure T H hH hspec hT hHC hcanon)

end TCSlib.Cryptography.SecureComputation
