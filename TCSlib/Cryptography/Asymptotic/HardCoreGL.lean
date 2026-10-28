/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter as a machine

The recovery procedure of [PS10, Algorithm 89.6] (`HardcoreBit.guessRecover`,
[Gar26, Figure 2.5]) as a polynomial-time string function: for each bit position `i < m` and
each nonempty `L ⊆ [k]` it queries the predictor `A` on `⟨1^n, Y ‖ (S_L ⊕ e_i)⟩` with fresh
coins and votes `B_L ⊕ A(…)`; bit `i` is the majority of its `2^k − 1` votes. The
`m (2^k − 1)` rounds are one guarded state loop (`GLLoop`, run through
`polyTimeComputable_stateIterate`) whose rounds are driven by a **table** hard-wired as
advice: the list of all pairs `⟨e_i, β_L⟩` (`β_L` the indicator string of `L`) in a fixed
order (`glTable`), so that no counter arithmetic is needed; the subset XORs `S_L`, `B_L` are
`selXorFun`/`ipFun`, the majorities `Complexity.polyTimeComputable_blockMap` with
`Complexity.polyTimeComputable_majority`.

The nonempty subsets are enumerated by `nesubsetEquiv : NESubset k ≃ Fin (2^k − 1)`
(`Fintype.equivFin` and `HardcoreBit.card_nonempty_finset`); the coins of the machine split
as the `GuessCoins` of the concrete inverter followed by unread coins (`glCoinsEquiv`).

## Main definitions

* `TCSlib.Cryptography.nesubsetEquiv`, `TCSlib.Cryptography.betaOf` — the enumeration of the
  nonempty subsets of `[k]` and their indicator strings.
* `TCSlib.Cryptography.GLLoop.start`, `GLLoop.step`, `GLLoop.out` — the voting loop.
* `TCSlib.Cryptography.glVotesFun`, `TCSlib.Cryptography.glRecoverFun` — the votes of all
  rounds and the recovered string (majorities of the votes).

## Main results

* `TCSlib.Cryptography.GLLoop.orbit_eq` — the closed form of the voting loop.
* `TCSlib.Cryptography.glRecoverFun_input` — the recovered string is
  `List.ofFn (guessRecover A' k Y c)` on the well-formed input.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

/-! ## Enumerating the nonempty subsets -/

/-- The nonempty subsets of `[k]` enumerated by `Fin (2^k − 1)` (noncomputable; it only
indexes the advice table and the coin blocks). -/
noncomputable def nesubsetEquiv (k : ℕ) : HardcoreBit.NESubset k ≃ Fin (2 ^ k - 1) :=
  (Fintype.equivFin _).trans (finCongr (by rw [HardcoreBit.card_nonempty_finset, Fintype.card_fin]))

/-- The indicator string of the `j`-th nonempty subset. -/
noncomputable def betaOf {k : ℕ} (j : Fin (2 ^ k - 1)) : Fin k → Bool :=
  fun t => decide (t ∈ ((nesubsetEquiv k).symm j).1)

/-- The subset with indicator string `betaOf j` is the `j`-th nonempty subset. -/
theorem filter_betaOf {k : ℕ} (j : Fin (2 ^ k - 1)) :
    univ.filter (fun t : Fin k => betaOf j t = true) = ((nesubsetEquiv k).symm j).1 := by
  ext t
  simp [betaOf]

/-- The number of `true`s of an encoded string is the cardinality of its support. -/
theorem count_true_ofFn {M : ℕ} (v : Fin M → Bool) :
    (List.ofFn v).count true = #(univ.filter fun j : Fin M => v j = true) := by
  rw [Finset.card_filter]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun j => v j.succ), Fin.sum_univ_succ]
    cases v 0 <;> simp [add_comm]

/-! ## The voting loop -/

namespace GLLoop

/-- The fixed data of the loop: `⟨⟨⟨1^n, Y⟩, α⟩, ⟨⟨1^m, 1^k⟩, ⟨1^{|ρ|}, ⟨s, b⟩⟩⟩⟩` (the layout of
`A`'s input slots, then the unary lengths, the coins of `A` in unary and the `GuessCoins`
strings `s`, `b`). -/
def fixed (u Y α um uk ur s b : List Bool) : List Bool :=
  NUPPT.layout u Y α (pairEncode (pairEncode um uk) (pairEncode ur (pairEncode s b)))

/-- The input of the loop: the fixed data, the table and the coin blocks. -/
def input (fx tbl cs : List Bool) : List Bool := pairEncode fx (pairEncode tbl cs)

/-- The initial state `⟨tbl, ⟨cs, []⟩⟩`: the whole table, all coin blocks, no votes. -/
def start (x : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD x)) (pairEncode (pairSndD (pairSndD x)) [])

/-- The projections of the fixed data out of a state word `⟨⟨fx, ⟨tbl, cs⟩⟩, ⟨tbl', ⟨cs', votes⟩⟩⟩`. -/
def fx (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- The unary parameter `1^n`. -/
def pu (w : List Bool) : List Bool := NUPPT.inParam (fx w)

/-- The string `Y` passed to `A`. -/
def pY (w : List Bool) : List Bool := NUPPT.inArg (fx w)

/-- The advice of `A`. -/
def pα (w : List Bool) : List Bool := NUPPT.inAdvice (fx w)

/-- The unary block length `1^m`. -/
def pum (w : List Bool) : List Bool := pairFstD (pairFstD (NUPPT.inCoins (fx w)))

/-- The unary number of guessed bits `1^k`. -/
def puk (w : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inCoins (fx w)))

/-- The unary coin length `1^{|ρ|}` of `A`. -/
def pur (w : List Bool) : List Bool := pairFstD (pairSndD (NUPPT.inCoins (fx w)))

/-- The strings `s_1 ⋯ s_k`. -/
def ps (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (NUPPT.inCoins (fx w))))

/-- The guessed bits `b_1 ⋯ b_k`. -/
def pb (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (NUPPT.inCoins (fx w))))

/-- The remaining table. -/
def ptbl (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining coin blocks. -/
def pcs (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- The votes so far. -/
def pvotes (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The current table entry `⟨e_i, β_L⟩`: the first `|⟨1^m, 1^k⟩|` bits of the remaining table. -/
def entry (w : List Bool) : List Bool := (ptbl w).take (pairEncode (pum w) (puk w)).length

/-- The vote of the current round: `B_L ⊕ [A(1^n, Y ‖ (S_L ⊕ e_i); c) = 1]`. -/
def vote (A : NUPPT) (w : List Bool) : Bool :=
  xor ((ipFun (pairEncode (pairSndD (entry w)) (pb w))).headD false)
    (decide (A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) = [true]))

/-- The step: if the table is exhausted, stay; otherwise consume one entry and one coin block
and append the round's vote. -/
def step (A : NUPPT) (w : List Bool) : List Bool :=
  if ptbl w = [] then pairSndD w else
    pairEncode ((ptbl w).drop (pairEncode (pum w) (puk w)).length)
      (pairEncode ((pcs w).drop (pur w).length) (pvotes w ++ [vote A w]))

/-- The output: the votes of the final state. -/
def out (w : List Bool) : List Bool := pvotes w

/-- The length bound on the states. -/
def bound : PolyExpr := .add (.mul (.const 2) .var) (.const 2)

/-- When the table is exhausted the step is stationary. -/
theorem step_of_table_nil (A : NUPPT) (w : List Bool) (h : ptbl w = []) : step A w = pairSndD w := by
  unfold step
  rw [if_pos h]

/-- The projection `fx` is polynomial-time. -/
theorem fx_poly : PolyTimeComputable fx := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
/-- The projection `pu` is polynomial-time. -/
theorem pu_poly : PolyTimeComputable pu := NUPPT.polyTimeComputable_inParam.comp fx_poly
/-- The projection `pY` is polynomial-time. -/
theorem pY_poly : PolyTimeComputable pY := NUPPT.polyTimeComputable_inArg.comp fx_poly
/-- The projection `pα` is polynomial-time. -/
theorem pα_poly : PolyTimeComputable pα := NUPPT.polyTimeComputable_inAdvice.comp fx_poly
/-- The projection `pum` is polynomial-time. -/
theorem pum_poly : PolyTimeComputable pum :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `puk` is polynomial-time. -/
theorem puk_poly : PolyTimeComputable puk :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `pur` is polynomial-time. -/
theorem pur_poly : PolyTimeComputable pur :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly))
/-- The projection `ps` is polynomial-time. -/
theorem ps_poly : PolyTimeComputable ps :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly)))
/-- The projection `pb` is polynomial-time. -/
theorem pb_poly : PolyTimeComputable pb :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp (NUPPT.polyTimeComputable_inCoins.comp fx_poly)))
/-- The projection `ptbl` is polynomial-time. -/
theorem ptbl_poly : PolyTimeComputable ptbl := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
/-- The projection `pcs` is polynomial-time. -/
theorem pcs_poly : PolyTimeComputable pcs :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
/-- The projection `pvotes` is polynomial-time. -/
theorem pvotes_poly : PolyTimeComputable pvotes :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
/-- The projection `entry` is polynomial-time. -/
theorem entry_poly : PolyTimeComputable entry :=
  takeLen_poly (pum_poly.pairEncode puk_poly) ptbl_poly


/-- The vote of a round is polynomial-time (`ipFun`, `selXorFun`, `A.output` on the layout,
the verdict test `polyTimeComputable_pairEq`). 

**Proof sketch.** The bit `B_L` is `headBit_poly` after `ipFun_poly`; the query is the pairing of `pY` with the XOR (`zipXor_poly`) of `selXorFun` and the unit vector; `A.output` on the layout is `A.polyTimeComputable_output` after `polyTimeComputable_layout`; the verdict test is `polyTimeComputable_pairEq`; the two bits are combined by `xor_poly`. -/
theorem vote_poly (A : NUPPT) : PolyTimeComputable fun w => [vote A w] := by
  have hβ : PolyTimeComputable fun w => pairSndD (entry w) :=
    polyTimeComputable_pairSndD.comp entry_poly
  have hB : PolyTimeComputable fun w => [(ipFun (pairEncode (pairSndD (entry w)) (pb w))).headD false] :=
    ptcComp headBit_poly (ptcComp ipFun_poly (hβ.pairEncode pb_poly))
  have hq : PolyTimeComputable fun w => pairEncode (pY w) (List.zipWith xor
      (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))) :=
    pY_poly.pairEncode (zipXor_poly (ptcComp selXorFun_poly ((pum_poly.pairEncode hβ).pairEncode ps_poly))
      (polyTimeComputable_pairFstD.comp entry_poly))
  have hans : PolyTimeComputable fun w => A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) :=
    ptcComp A.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout pu_poly hq pα_poly (takeLen_poly pur_poly pcs_poly))
  have htest : PolyTimeComputable fun w => [decide (A.output (NUPPT.layout (pu w)
      (pairEncode (pY w) (List.zipWith xor
        (selXorFun (pairEncode (pairEncode (pum w) (pairSndD (entry w))) (ps w))) (pairFstD (entry w))))
      (pα w) ((pcs w).take (pur w).length)) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hans.pairEncode (polyTimeComputable_const [true])) using 1
    funext w
    simp
  exact xor_poly hB htest

/-- The step is polynomial-time. -/
theorem step_poly (A : NUPPT) : PolyTimeComputable (step A) := by
  have hbody : PolyTimeComputable fun w =>
      pairEncode ((ptbl w).drop (pairEncode (pum w) (puk w)).length)
        (pairEncode ((pcs w).drop (pur w).length) (pvotes w ++ [vote A w])) :=
    (dropLen_poly (pum_poly.pairEncode puk_poly) ptbl_poly).pairEncode
      ((dropLen_poly pur_poly pcs_poly).pairEncode (pvotes_poly.append (vote_poly A)))
  have htest : PolyTimeComputable fun w => [decide (ptbl w = [])] := isNil_poly.comp ptbl_poly
  convert polyTimeComputable_ite htest polyTimeComputable_pairSndD hbody using 1
  funext w
  simp only [step, decide_eq_true_eq]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_const []))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := pvotes_poly


/-! ### The well-formed input and the closed form of the orbit -/

/-- The table entry for the round `p = (i, j)`: `⟨e_i, β_j⟩` with `e_i` the unit vector and `β_j`
the indicator string of the `j`-th nonempty subset. -/
noncomputable def glEntry (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) : List Bool :=
  pairEncode (List.ofFn (Pi.single p.divNat true : Fin m → Bool)) (List.ofFn (betaOf p.modNat))

/-- Every table entry has length `2m + 2 + k`. -/
theorem length_glEntry (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) :
    (glEntry m k p).length = 2 * m + 2 + k := by
  simp [glEntry, length_pairEncode]

/-- The table entry as a block of `2m + 2 + k` bits. -/
noncomputable def glEntryFn (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) : Fin (2 * m + 2 + k) → Bool :=
  fun v => (glEntry m k p).getD v false

/-- The block of an entry encodes the entry. -/
theorem ofFn_glEntryFn (m k : ℕ) (p : Fin (m * (2 ^ k - 1))) :
    List.ofFn (glEntryFn m k p) = glEntry m k p := by
  refine List.ext_getElem (by simp [length_glEntry]) fun v hv₁ hv₂ => ?_
  simp [glEntryFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv₂]

/-- **The advice table** of all rounds: the entries `⟨e_i, β_j⟩` in the order of
`Fin (m · (2^k − 1))`. -/
noncomputable def glTable (m k : ℕ) : List Bool := blocksStr (glEntryFn m k)

/-- The well-formed loop input: the fixed data with `s`, `b`, the table, and the coin blocks
followed by unread coins `ex`. -/
noncomputable def wfInput (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool) :
    List Bool :=
  input (fixed (List.replicate n true) Y (A.advice n) (List.replicate m true)
    (List.replicate k true) (List.replicate (A.coinLen n) true) (blocksStr s) (List.ofFn b))
    (glTable m k) (blocksStr cs ++ ex)

/-- The vote of the round `p = (i, j)` on the well-formed input:
`B_{L_j} ⊕ [A(1^n, Y ‖ (S_{L_j} ⊕ e_i); c_p) = 1]`. -/
noncomputable def wfVote (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool)
    (p : Fin (m * (2 ^ k - 1))) : Bool :=
  xor (HardcoreBit.ip (betaOf p.modNat) b)
    (decide (A.runAtL n (pairEncode Y (List.ofFn
      (∑ t ∈ univ.filter (fun t : Fin k => betaOf p.modNat t = true), s t + Pi.single p.divNat true)))
      (List.ofFn (cs p)) = [true]))

section Spec

variable (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool) (b : Fin k → Bool)
  (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool)

/-- The fixed data of a well-formed state word. -/
theorem fx_wf (st : List Bool) : fx (pairEncode (wfInput A n m k Y s b cs ex) st) =
    fixed (List.replicate n true) Y (A.advice n) (List.replicate m true) (List.replicate k true)
      (List.replicate (A.coinLen n) true) (blocksStr s) (List.ofFn b) := by
  simp [fx, wfInput, input]

/-- The block `t` of the coin blocks followed by unread coins. -/
theorem take_drop_coins (t : ℕ) (ht : t < m * (2 ^ k - 1)) :
    (((blocksStr cs ++ ex).drop (t * A.coinLen n)).take (A.coinLen n)) = List.ofFn (cs ⟨t, ht⟩) := by
  have h1 : t * A.coinLen n ≤ (blocksStr cs).length := by
    rw [length_blocksStr]; exact Nat.mul_le_mul_right _ ht.le
  rw [List.drop_append_of_le_length h1, List.take_append_of_le_length, take_drop_blocksStr cs ⟨t, ht⟩]
  rw [List.length_drop, length_blocksStr]
  have : (t + 1) * A.coinLen n ≤ m * (2 ^ k - 1) * A.coinLen n := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at this
  omega

/-- Dropping one more block of the coin blocks followed by unread coins. -/
theorem drop_drop_coins (t : ℕ) :
    ((blocksStr cs ++ ex).drop (t * A.coinLen n)).drop (A.coinLen n) =
      (blocksStr cs ++ ex).drop ((t + 1) * A.coinLen n) := by
  rw [List.drop_drop, Nat.succ_mul]

/-- The closed form of the orbit on the well-formed input, for `t ≤ m (2^k − 1)` rounds:
`⟨table.drop (t · entry), ⟨coins.drop (t · |ρ|), votes of the first t rounds⟩⟩`. 

**Proof sketch.** Induction on `t`. The table is not exhausted before round `m(2^k − 1)` (`List.drop_eq_nil_iff`, `length_blocksStr`), so the step consumes the entry `t` (`take_drop_blocksStr`, `ofFn_glEntryFn`), whose components are `e_i` and `β_j`; the vote is `wfVote` by `ipFun_ofFn`, `selXorFun_input`, `zipWith_xor_ofFn`, `take_drop_coins` and `NUPPT.runAtL_eq_output_layout`; the table and coin components advance by `List.drop_drop` (`drop_drop_coins`) and the votes by `List.ofFn_succ'`. -/
theorem orbit_eq (t : ℕ) (ht : t ≤ m * (2 ^ k - 1)) :
    orbit start (step A) (wfInput A n m k Y s b cs ex) t =
      pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
        (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
          (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)) := by
  induction t with
  | zero =>
    simp [orbit_zero, start, wfInput, input]
  | succ t ih =>
    have ht' : t < m * (2 ^ k - 1) := ht
    rw [orbit_succ, ih (Nat.le_of_succ_le ht)]
    have hne : (glTable m k).drop (t * (2 * m + 2 + k)) ≠ [] := by
      rw [Ne, List.drop_eq_nil_iff, glTable, length_blocksStr]
      intro h
      have : (t + 1) * (2 * m + 2 + k) ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
        Nat.mul_le_mul_right _ ht'
      rw [Nat.succ_mul] at this
      omega
    have hentry : entry (pairEncode (wfInput A n m k Y s b cs ex)
        (pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
          (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
            (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)))) =
        glEntry m k ⟨t, ht'⟩ := by
      simp only [entry, ptbl, pairFstD_pairEncode, pairSndD_pairEncode, pum, puk, fx_wf, fixed,
        NUPPT.inCoins_layout, length_pairEncode, List.length_replicate, glTable]
      rw [take_drop_blocksStr (glEntryFn m k) ⟨t, ht'⟩, ofFn_glEntryFn]
    have hvote : vote A (pairEncode (wfInput A n m k Y s b cs ex)
        (pairEncode ((glTable m k).drop (t * (2 * m + 2 + k)))
          (pairEncode ((blocksStr cs ++ ex).drop (t * A.coinLen n))
            (List.ofFn fun u : Fin t => wfVote A n m k Y s b cs ⟨u, by omega⟩)))) =
        wfVote A n m k Y s b cs ⟨t, ht'⟩ := by
      unfold vote
      rw [hentry]
      simp only [glEntry, pairFstD_pairEncode, pairSndD_pairEncode, pu, pY, pα, pum, pb, ps, pur,
        pcs, fx_wf, fixed, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
        NUPPT.inCoins_layout, List.length_replicate, ipFun_ofFn, List.headD_cons,
        take_drop_coins A n m k cs ex t ht']
      have hin : pairEncode (pairEncode (List.replicate m true)
          (List.ofFn (betaOf (Fin.modNat ⟨t, ht'⟩)))) (blocksStr s) =
          SelXor.input m (betaOf (Fin.modNat ⟨t, ht'⟩)) s := rfl
      rw [hin, selXorFun_input, zipWith_xor_ofFn, ← NUPPT.runAtL_eq_output_layout]
      rfl
    unfold step
    rw [if_neg (by simpa [ptbl] using hne), hvote]
    simp only [ptbl, pairFstD_pairEncode, pairSndD_pairEncode, pum, puk, pur, pcs, pvotes, fx_wf,
      fixed, NUPPT.inCoins_layout, length_pairEncode, List.length_replicate]
    refine congrArg₂ pairEncode ?_ (congrArg₂ pairEncode ?_ ?_)
    · rw [List.drop_drop, show t * (2 * m + 2 + k) + (2 * m + 2 + k) = (t + 1) * (2 * m + 2 + k) by ring]
    · exact drop_drop_coins A n m k cs ex t
    · rw [List.ofFn_succ', List.concat_eq_append]
      rfl

/-- After `m (2^k − 1)` rounds the loop is stationary (the table is exhausted). -/
theorem orbit_stable (j : ℕ) :
    orbit start (step A) (wfInput A n m k Y s b cs ex) (m * (2 ^ k - 1) + j) =
      orbit start (step A) (wfInput A n m k Y s b cs ex) (m * (2 ^ k - 1)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, orbit_succ, ih, orbit_eq A n m k Y s b cs ex _ le_rfl]
    have h0 : (glTable m k).drop (m * (2 ^ k - 1) * (2 * m + 2 + k)) = [] :=
      List.drop_eq_nil_of_le (by rw [glTable, length_blocksStr])
    rw [step_of_table_nil, pairSndD_pairEncode]
    simp only [ptbl, pairFstD_pairEncode, pairSndD_pairEncode]
    exact h0

/-- Every state of the loop on the well-formed input has length at most `2|input| + 2`. -/
theorem orbit_length_le (t : ℕ) :
    (orbit start (step A) (wfInput A n m k Y s b cs ex) t).length ≤
      bound.eval (wfInput A n m k Y s b cs ex).length := by
  have key : ∀ t ≤ m * (2 ^ k - 1), (orbit start (step A) (wfInput A n m k Y s b cs ex) t).length ≤
      bound.eval (wfInput A n m k Y s b cs ex).length := by
    intro t ht
    rw [orbit_eq A n m k Y s b cs ex t ht]
    simp only [bound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
      wfInput, input, length_pairEncode, List.length_drop, List.length_ofFn, glTable,
      length_blocksStr, List.length_append]
    have : t ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
      ht.trans (Nat.le_mul_of_pos_right _ (by omega))
    omega
  rcases le_or_gt t (m * (2 ^ k - 1)) with ht | ht
  · exact key t ht
  · obtain ⟨j, rfl⟩ : ∃ j, t = m * (2 ^ k - 1) + j := ⟨t - m * (2 ^ k - 1), by omega⟩
    rw [orbit_stable]
    exact key _ le_rfl

end Spec

end GLLoop

/-! ## The votes and the recovered string -/

/-- **The votes of all rounds**: the voting loop run for `|⟨x, start x⟩|` rounds. -/
def glVotesFun (A : NUPPT) (x : List Bool) : List Bool :=
  GLLoop.out ((gstep (GLLoop.step A) GLLoop.bound)^[(pairEncode x (GLLoop.start x)).length]
    (pairEncode x (GLLoop.start x)))

/-- The votes are polynomial-time. -/
theorem glVotesFun_poly (A : NUPPT) : PolyTimeComputable (glVotesFun A) :=
  polyTimeComputable_stateIterate GLLoop.start_poly (GLLoop.step_poly A) GLLoop.out_poly GLLoop.bound

/-- **The votes on the well-formed input** are the `m (2^k − 1)` round votes `wfVote`. -/
theorem glVotesFun_wfInput (A : NUPPT) (n m k : ℕ) (Y : List Bool) (s : Fin k → Fin m → Bool)
    (b : Fin k → Bool) (cs : Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool) :
    glVotesFun A (GLLoop.wfInput A n m k Y s b cs ex) =
      List.ofFn (GLLoop.wfVote A n m k Y s b cs) := by
  unfold glVotesFun
  set R := (pairEncode (GLLoop.wfInput A n m k Y s b cs ex)
    (GLLoop.start (GLLoop.wfInput A n m k Y s b cs ex))).length with hR
  have hRk : m * (2 ^ k - 1) ≤ R := by
    rw [hR, length_pairEncode, GLLoop.wfInput, GLLoop.input, length_pairEncode, length_pairEncode,
      GLLoop.glTable, length_blocksStr]
    have : m * (2 ^ k - 1) ≤ m * (2 ^ k - 1) * (2 * m + 2 + k) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [gstep_iterate_eq GLLoop.start (GLLoop.step A) GLLoop.bound _ R
    (fun i _ => GLLoop.orbit_length_le A n m k Y s b cs ex i) R le_rfl]
  obtain ⟨j, hj⟩ : ∃ j, R = m * (2 ^ k - 1) + j := ⟨R - m * (2 ^ k - 1), by omega⟩
  rw [hj, GLLoop.orbit_stable, GLLoop.orbit_eq A n m k Y s b cs ex _ le_rfl, GLLoop.out,
    GLLoop.pvotes, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- The majority of each block of `|fst z|` bits of `snd z` (the function of
`Complexity.polyTimeComputable_blockMap` with `Complexity.polyTimeComputable_majority`). -/
def glMajFun (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / (pairFstD z).length)).flatMap fun i =>
    [decide ((((pairSndD z).drop (i * (pairFstD z).length)).take (pairFstD z).length).length <
      2 * (((pairSndD z).drop (i * (pairFstD z).length)).take (pairFstD z).length).count true)]

/-- The blockwise majority is polynomial-time. -/
theorem glMajFun_poly : PolyTimeComputable glMajFun :=
  polyTimeComputable_blockMap .var polyTimeComputable_majority

/-- **The blockwise majority of the votes** `W : Fin m → Fin M → Bool`, with block length `M`
(given in unary), is the string of the majorities `majority (W i)`, provided `M > 0` or `m = 0`. -/
theorem glMajFun_blocksStr {m M : ℕ} (hM : 0 < M ∨ m = 0) (W : Fin m → Fin M → Bool) :
    glMajFun (pairEncode (List.replicate M true) (blocksStr W)) =
      List.ofFn fun i : Fin m => HardcoreBit.majority (W i) := by
  unfold glMajFun
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, length_blocksStr]
  have hdiv : m * M / M = m := by
    rcases hM with hM | rfl
    · exact Nat.mul_div_cancel m hM
    · simp
  rw [hdiv, ← List.map_eq_flatMap]
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [take_drop_blocksStr W ⟨j, by simpa using hj₂⟩, List.length_ofFn, count_true_ofFn,
    HardcoreBit.majority, Fintype.card_fin]

/-- Unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{ab}` as a string function
(`Turing.FinTM.computesFunInTime_unaryMul`). -/
def unaryMulFun (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, v) => List.replicate (u.length * v.length) true
  | none => []

/-- Unary multiplication is polynomial-time. -/
theorem unaryMulFun_poly : PolyTimeComputable unaryMulFun := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  exact ⟨M, c, 2, hM⟩

/-- Unary multiplication on a pair of unary strings. -/
theorem unaryMulFun_pairEncode (a b : ℕ) :
    unaryMulFun (pairEncode (List.replicate a true) (List.replicate b true)) =
      List.replicate (a * b) true := by
  simp [unaryMulFun, pairDecode_pairEncode]


end TCSlib.Cryptography

/-! ## The Goldreich–Levin recovery machine -/

namespace Complexity.NUPPT

/-- **Pre-processing as a definition** (the witness of `exists_comp` with `post = id`): the
machine with `A`'s coins and advice that runs `A(1^n, pre y)`. -/
noncomputable def precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    NUPPT :=
  ofPolyTime (A.polyTimeComputable_output.comp
    (polyTimeComputable_layout polyTimeComputable_inParam (hpre.comp polyTimeComputable_inArg)
      polyTimeComputable_inAdvice polyTimeComputable_inCoins)) A.coins A.adv A.advice A.advice_length

/-- The pre-processed machine has the coins of `A`. -/
@[simp] theorem coins_precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre) :
    (A.precomp hpre).coins = A.coins := rfl

/-- The activation of the pre-processed machine. -/
theorem runAtL_precomp (A : NUPPT) {pre : List Bool → List Bool} (hpre : PolyTimeComputable pre)
    (n : ℕ) (y r : List Bool) : (A.precomp hpre).runAtL n y r = A.runAtL n (pre y) r := by
  unfold precomp
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

end Complexity.NUPPT

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

namespace GLRaw

/-- The Goldreich–Levin advice `⟨1^k, ⟨1^M, table⟩⟩` slot of the raw input. -/
def adv (z : List Bool) : List Bool := pairFstD (NUPPT.inAdvice z)

/-- The advice of `A`. -/
def α (z : List Bool) : List Bool := pairSndD (NUPPT.inAdvice z)

/-- The unary `1^k`. -/
def uk (z : List Bool) : List Bool := pairFstD (adv z)

/-- The unary `1^M`, `M = 2^k − 1`. -/
def uM (z : List Bool) : List Bool := pairFstD (pairSndD (adv z))

/-- The table. -/
def tbl (z : List Bool) : List Bool := pairSndD (pairSndD (adv z))

/-- The unary block length `1^{m(n)}`. -/
def um (mP : PolyExpr) (z : List Bool) : List Bool :=
  List.replicate (mP.eval (NUPPT.inParam z).length) true

/-- The unary coin length `1^{|ρ|}` of `A`. -/
def ur (A : NUPPT) (z : List Bool) : List Bool :=
  List.replicate (A.coins.eval (NUPPT.inParam z).length) true

/-- The unary `1^{k·m}`. -/
def ukm (mP : PolyExpr) (z : List Bool) : List Bool := unaryMulFun (pairEncode (uk z) (um mP z))

/-- The strings `s_1 ⋯ s_k`: the first `k·m` coins. -/
def cs₁ (mP : PolyExpr) (z : List Bool) : List Bool := (NUPPT.inCoins z).take (ukm mP z).length

/-- The coins after the first `k·m`. -/
def r₁ (mP : PolyExpr) (z : List Bool) : List Bool := (NUPPT.inCoins z).drop (ukm mP z).length

/-- The guessed bits `b_1 ⋯ b_k`: the next `k` coins. -/
def cb (mP : PolyExpr) (z : List Bool) : List Bool := (r₁ mP z).take (uk z).length

/-- The remaining coins: the blocks for the calls of `A`. -/
def cs₂ (mP : PolyExpr) (z : List Bool) : List Bool := (r₁ mP z).drop (uk z).length

/-- The projection `adv` is polynomial-time. -/
theorem adv_poly : PolyTimeComputable adv := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice
/-- The projection `α` is polynomial-time. -/
theorem α_poly : PolyTimeComputable α := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice
/-- The projection `uk` is polynomial-time. -/
theorem uk_poly : PolyTimeComputable uk := polyTimeComputable_pairFstD.comp adv_poly
/-- The projection `uM` is polynomial-time. -/
theorem uM_poly : PolyTimeComputable uM :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp adv_poly)
/-- The projection `tbl` is polynomial-time. -/
theorem tbl_poly : PolyTimeComputable tbl :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp adv_poly)
/-- The projection `um` is polynomial-time. -/
theorem um_poly (mP : PolyExpr) : PolyTimeComputable (um mP) := by
  unfold um
  exact ptcComp (g := fun x => List.replicate (mP.eval x.length) true)
    (polyTimeComputable_unaryPoly mP) NUPPT.polyTimeComputable_inParam
/-- The projection `ur` is polynomial-time. -/
theorem ur_poly (A : NUPPT) : PolyTimeComputable (ur A) := by
  unfold ur
  exact ptcComp (g := fun x => List.replicate (A.coins.eval x.length) true)
    (polyTimeComputable_unaryPoly A.coins) NUPPT.polyTimeComputable_inParam
/-- The projection `ukm` is polynomial-time. -/
theorem ukm_poly (mP : PolyExpr) : PolyTimeComputable (ukm mP) := by
  unfold ukm
  exact ptcComp (g := unaryMulFun) unaryMulFun_poly (uk_poly.pairEncode (um_poly mP))
/-- The projection `cs₁` is polynomial-time. -/
theorem cs₁_poly (mP : PolyExpr) : PolyTimeComputable (cs₁ mP) :=
  takeLen_poly (ukm_poly mP) NUPPT.polyTimeComputable_inCoins
/-- The projection `r₁` is polynomial-time. -/
theorem r₁_poly (mP : PolyExpr) : PolyTimeComputable (r₁ mP) :=
  dropLen_poly (ukm_poly mP) NUPPT.polyTimeComputable_inCoins
/-- The projection `cb` is polynomial-time. -/
theorem cb_poly (mP : PolyExpr) : PolyTimeComputable (cb mP) := takeLen_poly uk_poly (r₁_poly mP)
/-- The projection `cs₂` is polynomial-time. -/
theorem cs₂_poly (mP : PolyExpr) : PolyTimeComputable (cs₂ mP) := dropLen_poly uk_poly (r₁_poly mP)

end GLRaw

/-- **The raw recovery function** on the layout `⟨⟨⟨1^n, Y⟩, ⟨⟨1^k, ⟨1^M, table⟩⟩, α⟩⟩, r⟩`:
split the coins into `s` (`k·m` bits), `b` (`k` bits) and the call blocks, run the voting loop
on the fixed data `⟨⟨⟨1^n, Y⟩, α⟩, ⟨⟨1^m, 1^k⟩, ⟨1^{|ρ|}, ⟨s, b⟩⟩⟩⟩`, the table and the blocks,
and take the blockwise majority with block length `M`. -/
def glRawFun (A : NUPPT) (mP : PolyExpr) (z : List Bool) : List Bool :=
  glMajFun (pairEncode (GLRaw.uM z) (glVotesFun A (GLLoop.input
    (GLLoop.fixed (NUPPT.inParam z) (NUPPT.inArg z) (GLRaw.α z) (GLRaw.um mP z) (GLRaw.uk z)
      (GLRaw.ur A z) (GLRaw.cs₁ mP z) (GLRaw.cb mP z))
    (GLRaw.tbl z) (GLRaw.cs₂ mP z))))

/-- The raw recovery function is polynomial-time. -/
theorem glRawFun_poly (A : NUPPT) (mP : PolyExpr) : PolyTimeComputable (glRawFun A mP) := by
  unfold glRawFun
  exact ptcComp (g := glMajFun) glMajFun_poly (GLRaw.uM_poly.pairEncode
    (ptcComp (g := glVotesFun A) (glVotesFun_poly A)
      ((NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
        NUPPT.polyTimeComputable_inArg GLRaw.α_poly
        (((GLRaw.um_poly mP).pairEncode GLRaw.uk_poly).pairEncode
          ((GLRaw.ur_poly A).pairEncode ((GLRaw.cs₁_poly mP).pairEncode (GLRaw.cb_poly mP))))).pairEncode
        (GLRaw.tbl_poly.pairEncode (GLRaw.cs₂_poly mP)))))

/-- The Goldreich–Levin advice at `n`: `⟨1^{k(n)}, ⟨1^{2^{k(n)} − 1}, table⟩⟩`. -/
noncomputable def glAdvice (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (List.replicate (k n) true)
    (pairEncode (List.replicate (2 ^ k n - 1) true) (GLLoop.glTable (mP.eval n) (k n)))

/-- The coin polynomial of the recovery machine: `K·m + K + m·K·ρ`, a majorant of
`k·m + k + m(2^k − 1)·|ρ|` when `2^k ≤ K`. -/
def glCoins (mP K : PolyExpr) (A : NUPPT) : PolyExpr :=
  .add (.mul K mP) (.add K (.mul mP (.mul K A.coins)))

/-- The advice polynomial of the recovery machine. -/
def glAdvPoly (mP K : PolyExpr) (A : NUPPT) : PolyExpr :=
  .add (.mul (.const 2) (.add (.add (.mul (.const 4) K) (.const 4))
    (.mul (.mul mP K) (.add (.add (.mul (.const 2) mP) (.const 2)) K)))) (.add (.const 2) A.adv)

/-- `k ≤ 2^k`. -/
theorem le_two_pow (k : ℕ) : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le

/-- The advice of the recovery machine is polynomially bounded. -/
theorem length_glAdvice_le (mP K : PolyExpr) (A : NUPPT) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) : (pairEncode (glAdvice mP k n) (A.advice n)).length ≤ (glAdvPoly mP K A).eval n := by
  have hK := hk n
  have hkK : k n ≤ K.eval n := (le_two_pow (k n)).trans hK
  have hMK : 2 ^ k n - 1 ≤ K.eval n := (Nat.sub_le _ _).trans hK
  have hA := A.advice_length n
  simp only [glAdvice, glAdvPoly, length_pairEncode, List.length_replicate, GLLoop.glTable,
    length_blocksStr, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have htbl : mP.eval n * (2 ^ k n - 1) * (2 * mP.eval n + 2 + k n) ≤
      mP.eval n * K.eval n * (2 * mP.eval n + 2 + K.eval n) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hMK) (by omega)
  omega

/-- **The Goldreich–Levin recovery machine** [PS10, Algorithm 89.6] for a predictor `A`, the
block length `mP`, the guess count `k` with `2^{k(n)} ≤ K(n)`: advice `⟨glAdvice, A.advice n⟩`,
coins `glCoins`, output function `glRawFun`. -/
noncomputable def glMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  NUPPT.ofPolyTime (glRawFun_poly A mP) (glCoins mP K A) (glAdvPoly mP K A)
    (fun n => pairEncode (glAdvice mP k n) (A.advice n)) (length_glAdvice_le mP K A k hk)

/-- The coins of the recovery machine. -/
@[simp] theorem coins_glMachine (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : (glMachine A mP K k hk).coins = glCoins mP K A := rfl

/-- The number of coins actually read by the recovery machine at `n`. -/
def glNeed (A : NUPPT) (mP : PolyExpr) (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  k n * mP.eval n + (k n + mP.eval n * (2 ^ k n - 1) * A.coinLen n)

/-- The coins read are at most the coins available. -/
theorem glNeed_le (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) :
    glNeed A mP k n ≤ (glCoins mP K A).eval n := by
  have hK := hk n
  have hkK : k n ≤ K.eval n := (le_two_pow (k n)).trans hK
  have hMK : 2 ^ k n - 1 ≤ K.eval n := (Nat.sub_le _ _).trans hK
  simp only [glNeed, glCoins, PolyExpr.eval_add, PolyExpr.eval_mul, NUPPT.coinLen]
  have h1 : k n * mP.eval n ≤ K.eval n * mP.eval n := Nat.mul_le_mul_right _ hkK
  have h2 : mP.eval n * (2 ^ k n - 1) * A.coins.eval n ≤ mP.eval n * (K.eval n * A.coins.eval n) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hMK)
  omega

/-- **The recovery machine on well-formed coins** `s ‖ b ‖ blocks ‖ extra` computes the
blockwise majorities of the round votes: bit `i` is the majority over `j` of
`wfVote (i, j)`. 

**Proof sketch.** Unfold `runAtL_ofPolyTime` and the projections of the raw layout; the coin cuts at `k·m` (`unaryMulFun_pairEncode`) and `k` are `List.take_left'`/`drop_left'` on the concatenation `hr`; the loop input is `GLLoop.wfInput`, so the votes are `glVotesFun_wfInput`, which is `blocksStr` of the votes indexed by `finProdFinEquiv`; conclude with `glMajFun_blocksStr`. -/
theorem glMachine_runAt (A : NUPPT) (mP K : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, 2 ^ k n ≤ K.eval n)
    (n : ℕ) (Y : List Bool) (s : Fin (k n) → Fin (mP.eval n) → Bool) (b : Fin (k n) → Bool)
    (cs : Fin (mP.eval n * (2 ^ k n - 1)) → Fin (A.coinLen n) → Bool) (ex : List Bool)
    (r : (glMachine A mP K k hk).Coins n)
    (hr : List.ofFn r = blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex)
    (hM : 0 < 2 ^ k n - 1 ∨ mP.eval n = 0) :
    (glMachine A mP K k hk).runAt n Y r =
      List.ofFn fun i : Fin (mP.eval n) => HardcoreBit.majority fun j : Fin (2 ^ k n - 1) =>
        GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs (finProdFinEquiv (i, j)) := by
  rw [NUPPT.runAt_eq]
  unfold glMachine
  rw [NUPPT.runAtL_ofPolyTime]
  unfold glRawFun
  simp only [GLRaw.uM, GLRaw.adv, GLRaw.α, GLRaw.uk, GLRaw.tbl, GLRaw.um, GLRaw.ur, GLRaw.ukm,
    GLRaw.cs₁, GLRaw.r₁, GLRaw.cb, GLRaw.cs₂, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, glAdvice,
    List.length_replicate, unaryMulFun_pairEncode, hr]
  have h1 : (blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex).take (k n * mP.eval n) = blocksStr s := by
    simp only [List.append_assoc]
    exact List.take_left' (length_blocksStr s)
  have h2 : (blocksStr s ++ List.ofFn b ++ blocksStr cs ++ ex).drop (k n * mP.eval n) =
      List.ofFn b ++ (blocksStr cs ++ ex) := by
    simp only [List.append_assoc]
    exact List.drop_left' (length_blocksStr s)
  rw [h1, h2, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  have hin : GLLoop.input (GLLoop.fixed (List.replicate n true) Y (A.advice n)
      (List.replicate (mP.eval n) true) (List.replicate (k n) true)
      (List.replicate (A.coins.eval n) true) (blocksStr s) (List.ofFn b))
      (GLLoop.glTable (mP.eval n) (k n)) (blocksStr cs ++ ex) =
      GLLoop.wfInput A n (mP.eval n) (k n) Y s b cs ex := rfl
  rw [hin, glVotesFun_wfInput]
  have hW : List.ofFn (GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs) =
      blocksStr fun i j => GLLoop.wfVote A n (mP.eval n) (k n) Y s b cs (finProdFinEquiv (i, j)) := by
    unfold blocksStr
    congr 1
    funext p
    rw [blocksEquiv_symm_apply]
    congr 1
    exact (finProdFinEquiv.apply_symm_apply p).symm
  rw [hW, glMajFun_blocksStr hM]


/-! ## A bound on powers of two -/

/-- `2^{size x} ≤ 2x + 1`. -/
theorem two_pow_size_le (x : ℕ) : 2 ^ Nat.size x ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hpos : 0 < Nat.size x := Nat.size_pos.mpr hx
    have h := Nat.lt_size.mp (Nat.sub_lt hpos Nat.one_pos)
    calc 2 ^ Nat.size x = 2 * 2 ^ (Nat.size x - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hpos]
      _ ≤ 2 * x + 1 := by omega


/-! ## Majorities under reindexing -/

/-- The majority is invariant under a bijective reindexing of the votes. -/
theorem majority_comp_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ'] (σ : κ' ≃ κ) (v : κ → Bool) :
    HardcoreBit.majority (fun x => v (σ x)) = HardcoreBit.majority v := by
  classical
  unfold HardcoreBit.majority
  have hcard : #(univ.filter fun x => v (σ x) = true) = #(univ.filter fun y => v y = true) := by
    rw [← Finset.card_map σ.toEmbedding]
    congr 1
    ext y
    simp [Finset.mem_map_equiv]
  rw [Fintype.card_congr σ, hcard]

/-! ## The coins of the recovery machine as `GuessCoins` -/

/-- A tuple of blocks with values in an arbitrary type as a function of the flattened index
(`blocksEquiv` for an arbitrary codomain). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- The coins of the concrete inverter (`GuessCoins`) together with unread coins, as the coin
string of the recovery machine: `s` as `k` blocks of `m` bits, then `b`, then the call blocks
indexed by `(i, j)` with `j` the enumeration of the subsets, then the unread coins. -/
noncomputable def glCoinsEquiv (A : NUPPT) (n m k Q : ℕ)
    (hQ : k * m + (k + m * (2 ^ k - 1) * A.coinLen n) ≤ Q) :
    HardcoreBit.GuessCoins m k (A.Coins n) × (Fin (Q - (k * m + (k + m * (2 ^ k - 1) * A.coinLen n))) → Bool) ≃
      (Fin Q → Bool) :=
  ((((blocksEquiv k m).symm.prodCongr ((Equiv.refl (Fin k → Bool)).prodCongr
      (((Equiv.refl (Fin m)).arrowCongr ((nesubsetEquiv k).arrowCongr (Equiv.refl (A.Coins n)))).trans
        ((blocksEquivX m (2 ^ k - 1) (A.Coins n)).symm.trans
          (blocksEquiv (m * (2 ^ k - 1)) (A.coinLen n)).symm)))).trans
    ((Equiv.refl _).prodCongr (Fin.appendEquiv k (m * (2 ^ k - 1) * A.coinLen n)))).trans
      (Fin.appendEquiv (k * m) (k + m * (2 ^ k - 1) * A.coinLen n))).prodCongr (Equiv.refl _) |>.trans
    ((Fin.appendEquiv _ _).trans (finCastEquiv (Nat.add_sub_cancel' hQ)))

/-- The call blocks `(i, L) ↦ c i L` as a function of the flattened round index `p = (i, j)`,
`L` the `j`-th nonempty subset (the transport of `c` along `glCoinsEquiv`). -/
noncomputable def glBlocks (A : NUPPT) (n m k : ℕ) (c : Fin m → HardcoreBit.NESubset k → A.Coins n) :
    Fin (m * (2 ^ k - 1)) → Fin (A.coinLen n) → Bool :=
  (blocksEquivX m (2 ^ k - 1) (A.Coins n)).symm
    (((Equiv.refl (Fin m)).arrowCongr ((nesubsetEquiv k).arrowCongr (Equiv.refl (A.Coins n)))) c)

/-- The call block of the round `p` is `c p.divNat L_{p.modNat}`. -/
@[simp] theorem glBlocks_apply (A : NUPPT) (n m k : ℕ) (c : Fin m → HardcoreBit.NESubset k → A.Coins n)
    (p : Fin (m * (2 ^ k - 1))) :
    glBlocks A n m k c p = c p.divNat ((nesubsetEquiv k).symm p.modNat) := rfl

/-- The encoding of the coins `(s, b, c)` with unread coins `ex`:
`s ‖ b ‖ blocks ‖ ex`. -/
theorem ofFn_glCoinsEquiv (A : NUPPT) (n m k Q : ℕ)
    (hQ : k * m + (k + m * (2 ^ k - 1) * A.coinLen n) ≤ Q)
    (g : HardcoreBit.GuessCoins m k (A.Coins n))
    (ex : Fin (Q - (k * m + (k + m * (2 ^ k - 1) * A.coinLen n))) → Bool) :
    List.ofFn (glCoinsEquiv A n m k Q hQ (g, ex)) =
      blocksStr g.1 ++ List.ofFn g.2.1 ++ blocksStr (glBlocks A n m k g.2.2) ++ List.ofFn ex := by
  obtain ⟨s, b, c⟩ := g
  simp only [glCoinsEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl,
    id]
  rw [ofFn_finCastEquiv, ofFn_appendEquiv, ofFn_appendEquiv, ofFn_appendEquiv]
  simp only [List.append_assoc]
  rfl


/-! ## The inversion probability of the family inverter -/

/-- The concrete predictor `A'` of [PS10, Algorithm 89.6] induced by a machine `A₁` at parameter
`n` and an encoding `enc` of the first argument: `A'(y, q) = [A₁(1^n, ⟨enc y, q⟩) = 1]`. -/
def glPredictorOf (A₁ : NUPPT) (n m : ℕ) {β : Type*} (enc : β → List Bool) :
    β × (Fin m → Bool) → A₁.Coins n → Bool :=
  fun p c => decide (A₁.runAtL n (pairEncode (enc p.1) (List.ofFn p.2)) (List.ofFn c) = [true])

/-- **The recovery machine computes `guessRecover`** on well-formed coins: for coins
`(s, b, c)` and unread coins `ex`, the answer on `y` is the encoding of
`guessRecover (glPredictor A n o m) k y (s, b, c)`.

**Proof sketch.** `glMachine_runAt` gives the blockwise majorities of the round votes; the
vote of the round `(i, L)` is `subsetSum L b ⊕ A'(y, subsetSum L s ⊕ e_i; c i L)` by
`filter_betaOf`, `ip_eq_sum_filter` and the projections of `finProdFinEquiv`; the majority over
`j : Fin (2^k − 1)` is the majority over `L : NESubset k` by `majority_comp_equiv`. -/
theorem glMachine_runAt_guessRecover (A₁ : NUPPT) (iP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ iP.eval n = 0)
    {β : Type*} (enc : β → List Bool) (y : β)
    (g : HardcoreBit.GuessCoins (iP.eval n) (k n) (A₁.Coins n))
    (ex : Fin ((glCoins iP K A₁).eval n - glNeed A₁ iP k n) → Bool) :
    (glMachine A₁ iP K k hk).runAt n (enc y)
        (glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (g, ex)) =
      List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (iP.eval n) enc) (k n) y g) := by
  obtain ⟨s, b, c⟩ := g
  rw [glMachine_runAt A₁ iP K k hk n (enc y) s b (glBlocks A₁ n (iP.eval n) (k n) c) (List.ofFn ex) _
    (ofFn_glCoinsEquiv A₁ n (iP.eval n) (k n) _ (glNeed_le A₁ iP K k hk n) (s, b, c) ex) hM]
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [← majority_comp_equiv (nesubsetEquiv (k n))]
  unfold HardcoreBit.guessRecover
  refine congrArg HardcoreBit.majority (funext fun L => ?_)
  simp only [GLLoop.wfVote, glBlocks_apply, glPredictorOf, HardcoreBit.subsetSum]
  have hdiv : (finProdFinEquiv (i, nesubsetEquiv (k n) L)).divNat = i :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i, nesubsetEquiv (k n) L))
  have hmod : (finProdFinEquiv (i, nesubsetEquiv (k n) L)).modNat = nesubsetEquiv (k n) L :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i, nesubsetEquiv (k n) L))
  simp only [hdiv, hmod, filter_betaOf, Equiv.symm_apply_apply, ip_eq_sum_filter]
  rfl

end TCSlib.Cryptography
