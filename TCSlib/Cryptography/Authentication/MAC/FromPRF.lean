/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Game
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Bound
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Complexity.Randomized.Repetition
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF MAC

[PS10, Protocol 134.3]: for a family `{f_s : {0,1}^n → {0,1}^n}`, `Gen(1^n)` samples a uniform
`n`-bit key, `Tag_k(m) = f_k(m)`, and `Ver_k(m, σ)` accepts iff `f_k(m) = σ`. Theorem 135.4: when
the family is pseudorandom, the MAC is secure.

**The construction.** `F` comes with its polynomial-time evaluator `E` on `⟨s, x⟩` (clause (1) of
the ch. 2–4 layer's `PRF`). `Gen` is the ch. 2–4 layer's coin-key machine (its coins are the key,
`runAt_coinKey`). `Tag` applies `E` to its argument, and `Ver` tests `E ⟨k, m⟩ = σ` with
`polyTimeComputable_pairEq`.

## Main definitions

* `Authentication.prfTagFun`, `Authentication.prfVerFun`: the tagging and verification functions.
* `Authentication.prfMAC`: Protocol 134.3 as a `MAC`, with correctness proved.

## Main results

* `Authentication.prfMAC_secure` (Thm 135.4, proved): a PRF gives a secure MAC, with the forgery
  probability at most `prfAdv(F_n, D) + 2^{-n}` at every `n` for a distinguisher `D`.

## Contents

* `MAC/FromPRF/Handler`: the reduction's handler (forwarded and stored queries, the final query).
* `MAC/FromPRF/Reduction`: the distinguisher, accepting against `f` iff the forger forges against
  the tagging oracle `f`.
* `MAC/FromPRF/Random`: forging against a random function succeeds with probability `≤ 2^{-t}`.
* `MAC/FromPRF/Game`: the forgery game of a MAC with a deterministic tag.
* `MAC/FromPRF/Bound`: the bound `Pr[forge] ≤ prfAdv + 2^{-n}` for a MAC whose tag is a keyed
  family.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 134.3 and Theorem 135.4 (book pp. 134–135).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The tagging function on the raw machine input: `E` applied to the argument `⟨k, m⟩`. -/
def prfTagFun (E : List Bool → List Bool) : List Bool → List Bool := E ∘ NUPPT.inArg

/-- The raw tagging function returns `E (NUPPT.inArg z)` on input `z`. -/
theorem prfTagFun_eq (E : List Bool → List Bool) (z : List Bool) :
    prfTagFun E z = E (NUPPT.inArg z) := rfl

/-- The verification function on `⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`: `[true]` iff `E ⟨k, m⟩ = σ`. -/
def prfVerFun (E : List Bool → List Bool) : List Bool → List Bool :=
  (fun z => [decide (pairFstD z = pairSndD z)]) ∘ fun w =>
    pairEncode (E (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairSndD w)))))
      (pairSndD (pairSndD (pairSndD w)))

/-- The raw verifier compares `E ⟨k, m⟩` with `σ`, using the three components decoded from
the input `w` [PS10, Protocol 134.3]. -/
theorem prfVerFun_eq (E : List Bool → List Bool) (w : List Bool) :
    prfVerFun E w =
      [decide (E (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairSndD w)))) =
        pairSndD (pairSndD (pairSndD w)))] := by
  simp only [prfVerFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The tagging function is polynomial-time. -/
theorem polyTimeComputable_prfTagFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfTagFun E) :=
  hE.comp NUPPT.polyTimeComputable_inArg

/-- The verification function is polynomial-time. -/
theorem polyTimeComputable_prfVerFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfVerFun E) := by
  refine polyTimeComputable_pairEq.comp ?_
  refine PolyTimeComputable.pairEncode ?_ ?_
  · exact hE.comp (PolyTimeComputable.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
  · exact polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- **The PRF MAC** [PS10, Protocol 134.3], with `n`-bit messages and tags, for a family `F` with
evaluator `E`. -/
noncomputable def prfMAC (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) : MAC where
  msgLen := .var
  tagLen := .var
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  tag := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0)
  ver := prfVerFun E
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  tag_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  ver_poly := polyTimeComputable_prfVerFun hE
  correct := by
    intro n m rg rt
    simp only [PolyExpr.eval_var] at m ⊢
    have hlen : (NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).coinLen n = n :=
      (NUPPT.coinLen_eq _ n).trans
        ((congrArg (fun p : PolyExpr => p.eval n)
          (NUPPT.coins_ofPolyTimeUniform polyTimeComputable_pairSndD .var)).trans
            (PolyExpr.eval_var n))
    let k : Fin n → Bool := fun j => rg (Fin.cast hlen.symm j)
    have hk : List.ofFn rg = List.ofFn k := List.ofFn_congr hlen rg
    simp only [runAt_coinKey, hk]
    simp only [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
      prfTagFun_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
      pairFstD_pairEncode, pairSndD_pairEncode, hFE, padFin_ofFn,
      prfVerFun_eq, atParam_eq, eq_self_iff_true, decide_true]

attribute [simps (config := { isSimp := false }) msgLen tagLen gen tag ver] prfMAC

/-- **Theorem 135.4: a PRF gives a secure MAC** [PS10, Theorem 135.4]: if `F` is a pseudorandom
function family, the PRF MAC is secure.

**Proof sketch** (the source's, with its bound `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}`).
1. Fix a forger `A` with budget `q`; let `ε(n)` be its forgery probability. `Gen` returns its
   coins, the key (`runAt_coinKey`, read at `n` bits by `NUPPT.coinsEquivPoly`); `Tag` returns
   `E ⟨k, m⟩ = f_k(m)` whatever its (empty) coins (`prfTagFun_eq`, `hFE`); `Ver` accepts `(m, σ)`
   iff `f_k(m) = σ` (`prfVerFun_eq`).
2. The distinguisher `D` (`PRFMAC.exists_macReduction`) runs `A` against its own oracle, answering
   each tagging query `m` with the oracle's value and storing `m` in its state. It then queries
   the oracle at `A`'s output message `m` and outputs `1` iff the answer is `σ` and `m` was not
   stored. It is T2 (`Games.exists_interactiveHandlerMachine`) for the handler
   `PRFMAC.macHandler` (`finCall = 1`, `outLen = 1`, budget `q + 1`) on the input-free companion
   of `A` (`Games.exists_toCompOn_of_toComp`), made an oracle adversary by T4
   (`Games.exists_toOracleAdversary_of_bitCodec`).
3. With the oracle `f_k`, `D` outputs `1` exactly when `A` forges (`PRFMAC.accept_forgeGame_eq`):
   probability `ε(n)`.
4. With a random function, a forgery is a guess of a fresh uniform value: probability at most
   `2^{-n}` (`PRFMAC.expect_fnForge_random_le`, sampling the function lazily by table override).
5. So `ε(n) ≤ prfAdv(F_n, D) + 2^{-n}` at every `n`, `n = 0` included
   (`PRFMAC.exists_forgeGame_le`), which is negligible (`PRF.negligible_prfAdv`, `Negligible.add`,
   `negligible_two_pow_neg`).

The PRF advantage is read through `OracleEnsemble.Indist`, in framework form after the F-1
restatement. -/
theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfMAC F E hE hFE).Secure := by
  -- `Gen` returns its coins, and `Tag` returns `E` of its argument.
  have hgen : ∀ n (rg : (prfMAC F E hE hFE).gen.Coins n),
      (prfMAC F E hE hFE).gen.runAt n [] rg = List.ofFn rg := by
    intro n
    have h : ∀ G : NUPPT, G = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var →
        ∀ rg : G.Coins n, G.runAt n [] rg = List.ofFn rg := by
      rintro G rfl rg
      exact runAt_coinKey .var n rg
    exact h _ (prfMAC_gen F E hE hFE)
  have htagE : ∀ n (w : List Bool) (rt : (prfMAC F E hE hFE).tag.Coins n),
      (prfMAC F E hE hFE).tag.runAt n w rt = E w := by
    intro n w
    have h : ∀ T : NUPPT,
        T = NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0) →
        ∀ rt : T.Coins n, T.runAt n w rt = E w := by
      rintro T rfl rt
      rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, prfTagFun_eq, NUPPT.inArg_eq,
        NUPPT.advInput_eq, pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode]
    exact h _ (prfMAC_tag F E hE hFE)
  -- The key is `Gen`'s coins, read at `n` bits.
  have hcoins : (prfMAC F E hE hFE).gen.coins = .var := by
    rw [prfMAC_gen, NUPPT.coins_ofPolyTimeUniform]
  let key : ∀ n, (prfMAC F E hE hFE).gen.Coins n ≃ (Fin n → Bool) := fun n =>
    (NUPPT.coinsEquivPoly hcoins n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool))
  have hkey : ∀ n rg, List.ofFn (key n rg) = List.ofFn rg := fun n rg => by
    rw [← NUPPT.coinsEquivPoly_ofFn hcoins n rg]
    exact (List.ofFn_congr (PolyExpr.eval_var n) _).symm
  have hmsg : ∀ n, (prfMAC F E hE hFE).msgLen.eval n = n := fun n => by
    rw [prfMAC_msgLen, PolyExpr.eval_var]
  have htl : ∀ n, (prfMAC F E hE hFE).tagLen.eval n = n := fun n => by
    rw [prfMAC_tagLen, PolyExpr.eval_var]
  -- On the key of `rg`, `E` computes `F_{key rg}` (`hFE`).
  have hEF : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool),
      E (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := by
    intro n rg m
    rw [hgen, ← hFE]
    rw [hkey, ofFn_padFin_of_length (by rw [List.length_ofFn, hmsg])]
  have htag : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
      (rt : (prfMAC F E hE hFE).tag.Coins n),
      (prfMAC F E hE hFE).tag.runAt n
          (pairEncode ((prfMAC F E hE hFE).gen.runAt n [] rg) (List.ofFn m)) rt =
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) := fun n rg m rt => by
    rw [htagE, hEF]
  have hacc : ∀ n rg (m : Fin ((prfMAC F E hE hFE).msgLen.eval n) → Bool)
      (σ : Fin ((prfMAC F E hE hFE).tagLen.eval n) → Bool),
      (prfMAC F E hE hFE).Accepts n ((prfMAC F E hE hFE).gen.runAt n [] rg) m σ ↔
        List.ofFn (F n (key n rg) (padFin n (List.ofFn m))) = List.ofFn σ := by
    intro n rg m σ
    rw [MAC.accepts_iff, prfMAC_ver, prfVerFun_eq, atParam_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hEF, List.singleton_inj, decide_eq_true_iff]
  -- The bound of the reduction, negligible.
  rw [MAC.secure_iff]
  intro A q
  obtain ⟨D, hD⟩ := PRFMAC.exists_forgeGame_le (prfMAC F E hE hFE) F hmsg htl key htag hacc A q
  exact ⟨_, (hF.negligible_prfAdv D (PRFMAC.macBudget q)).add negligible_two_pow_neg, hD⟩

end TCSlib.Cryptography.Authentication
