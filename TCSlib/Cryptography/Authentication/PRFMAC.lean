/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF MAC (statement phase)

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

* `Authentication.prfMAC_secure` (Thm 135.4, stated; a `sorry` under its sketch): a PRF gives a
  secure MAC.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 134.3 and Theorem 135.4 (book pp. 134–135).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The tagging function on the raw machine input: `E` applied to the argument `⟨k, m⟩`. -/
def prfTagFun (E : List Bool → List Bool) : List Bool → List Bool := E ∘ NUPPT.inArg

/-- The verification function on `⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`: `[true]` iff `E ⟨k, m⟩ = σ`. -/
def prfVerFun (E : List Bool → List Bool) : List Bool → List Bool :=
  (fun z => [decide (pairFstD z = pairSndD z)]) ∘ fun w =>
    pairEncode (E (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairSndD w)))))
      (pairSndD (pairSndD (pairSndD w)))

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
    rw [runAt_coinKey]
    have htag : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfTagFun hE) (.const 0)).runAt n
        (pairEncode (List.ofFn rg) (List.ofFn m)) rt = List.ofFn (F n rg m) := by
      rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
      simp [prfTagFun, NUPPT.inArg, NUPPT.advInput, hFE]
      rfl
    simp only [PolyExpr.eval_var] at m ⊢
    rw [htag, padFin_ofFn]
    simp [prfVerFun, atParam, hFE]
    rfl

/-- **Theorem 135.4: a PRF gives a secure MAC** [PS10, Theorem 135.4]: if `F` is a pseudorandom
function family, the PRF MAC is secure.

**Proof sketch** (the source's, with its bound).
1. Fix a forger `A` with budget `q`. Let `ε(n)` be its forgery probability against the PRF MAC.
2. The distinguisher `D` runs `A` against its own oracle, answering each tagging query `m` with
   the oracle's value. It then queries the oracle at `A`'s output message `m` and outputs `1`
   iff the answer is `σ` and `m` was not queried before.
3. With the oracle `f_k`, `D` outputs `1` exactly when `A` forges: probability `ε(n)`.
4. With a random function, a forgery is a guess of a fresh uniform value: probability at most
   `2^{-n}` (the collision bound `prob_mem_le`, or a direct count).
5. So `D`'s PRF advantage is at least `ε(n) − 2^{-n}`. Since `F` is a PRF it is negligible, so
   `ε` is negligible.
6. `D` is a machine by the efficiency result T1 (`Games.exists_handlerMachine`, the handler
   forwarding queries), and its budget is `q + 1`.

The PRF advantage is read through `OracleEnsemble.Indist`, in framework form after the F-1
restatement. -/
theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfMAC F E hE hFE).Secure := by
  sorry

end TCSlib.Cryptography.Authentication
