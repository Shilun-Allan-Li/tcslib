/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Lazy: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Lazy: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The rejecting experiment with lazily sampled tags

Step 3 of [PS10, Theorem 170.4] simulates the experiment that rejects fresh decryption queries by
a CPA adversary against the §3.9 scheme. That adversary cannot hold a random function on `2n`
bits; it samples the tags lazily, one tape per query, and answers decryption queries from the table
of its earlier answers. This file states that lazy experiment (`ettLazy`, with tapes in advance
`ettLazyTape`) and proves that it has the law of the rejecting experiment with a uniform random
tag function (`expect_ettImpl_lazy`).

**The lazy state** (`LSt n d`) is the recorded challenge and the table of the `Enc′` answers, newest
first: each entry is the pair `r ‖ c₁`, its tag and the encrypted message.
- `Enc′` on `m` with the nonce `r`: the tag of the pair `p = r ‖ c₁` is the table's tag at `p` if `p`
  is in the table, else the challenge's tag if `p` is the challenge's pair, else the query's tape
  (`tagOf`); the entry `(p, tag, m)` is added.
- `Dec′` on `w` refuses the record; a well-formed `w` whose pair is in the table and whose tag is the
  table's tag gets `⟨1, m⟩` with the table's message, every other word `⊥` (`lazyDec`).
- `Challenge` on `⟨m₀, m₁⟩`: the first time, as `Enc′` on `m_b` (without an entry), recorded.

**The law** (`expect_ettImpl_lazy`). Average the rejecting experiment over `R` with the table's tags
written over it (`tagTbl`, `ovr`). A new pair moves `R`'s value into the table (`expect_sample_ovr`);
a pair in the table has its tag; a decryption with a listed pair reads the table's tag, and its
answer `⟨1, c₁ ⊕ f(r)⟩` is the table's message, because the entry's pair is `r ‖ (m ⊕ f(r))` with an
`n`-bit `m` (`LInv`).

## Main definitions

* `ETTGame.LEntry`, `LSt`, `keysL`, `lookL`, `tagOf`, `lazyDec`, `tagTbl`, `LInv`.
* `ETTGame.lazyStep`, `ettLazyK`, `ettLazy`, `ettLazyTape`.

## Main results

* `ETTGame.expect_ettImpl_lazy`: the rejecting experiment with a random tag function is the lazy
  experiment.
* `ETTGame.expect_ettLazyTape`: the lazy experiment with tapes in advance.
* `ETTGame.tagTbl_none_nil`, `ETTGame.lInv_nil`: the empty lazy state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book pp. 170–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Tables -/

section Tables

variable {n d : ℕ}

/-- An entry of the lazy table: a pair, its tag and the message of the encryption. -/
abbrev LEntry (n : ℕ) : Type := (Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool

/-- `LEntry n = pair × tag × message`. -/
theorem LEntry_eq (n : ℕ) :
    LEntry n = ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool) × List Bool) := rfl

/-- The lazy state: the recorded challenge and the table, newest entry first. -/
abbrev LSt (n d : ℕ) : Type := Option (Fin d → Bool) × List (LEntry n)

/-- `LSt n d = Option (Fin d → Bool) × List (LEntry n)`. -/
theorem LSt_eq (n d : ℕ) : LSt n d = (Option (Fin d → Bool) × List (LEntry n)) := rfl

/-- The pairs of the table. -/
def keysL (L : List (LEntry n)) : List (Fin (2 * n) → Bool) := L.map Prod.fst

/-- `keysL L = L.map Prod.fst`. -/
theorem keysL_eq (L : List (LEntry n)) : keysL L = L.map Prod.fst := rfl

/-- **The table's entry at a pair:** the first (newest) entry with the pair `p`, if any. -/
def lookL (L : List (LEntry n)) (p : Fin (2 * n) → Bool) : Option (LEntry n) :=
  if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none

/-- `lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none`. -/
theorem lookL_eq (L : List (LEntry n)) (p : Fin (2 * n) → Bool) :
    lookL L p = if p ∈ keysL L then some (L.getD ((keysL L).idxOf p) default) else none := rfl

/-- **The tag of a pair:** the table's, else the challenge's at its pair, else none. -/
def tagOf (s : LSt n d) (p : Fin (2 * n) → Bool) : Option (Fin (2 * n) → Bool) :=
  match lookL s.2 p with
  | some e => some e.2.1
  | none =>
    match s.1 with
    | some c => if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
    | none => none

/-- `tagOf s p`: the table's tag, else the challenge's at its pair. -/
theorem tagOf_eq (s : LSt n d) (p : Fin (2 * n) → Bool) :
    tagOf s p = match lookL s.2 p with
      | some e => some e.2.1
      | none =>
        match s.1 with
        | some c =>
          if pairW n (List.ofFn c) = p then some (padFin (2 * n) (wT (List.ofFn c))) else none
        | none => none := rfl

/-- **The lazy decryption answer:** `⊥` on the record; on a well-formed word whose pair is in the
table with the word's tag, `⟨1, m⟩` with the table's message; `⊥` otherwise. -/
def lazyDec (s : LSt n d) (w : List Bool) : List Bool :=
  if (!refW s.1 w && wfW n w) = true then
    match lookL s.2 (pairW n w) with
    | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
    | none => []
  else []

/-- `lazyDec s w` unfolded. -/
theorem lazyDec_eq (s : LSt n d) (w : List Bool) :
    lazyDec s w = if (!refW s.1 w && wfW n w) = true then
      match lookL s.2 (pairW n w) with
      | some e => if List.ofFn e.2.1 = wT w then true :: e.2.2 else []
      | none => []
    else [] := rfl

/-- **The tag table of a lazy state:** the entries' tags, newest first, then the challenge's. -/
def tagTbl (s : LSt n d) : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)) :=
  s.2.map (fun e => (e.1, e.2.1)) ++
    match s.1 with
    | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
    | none => []

/-- `tagTbl s` unfolded. -/
theorem tagTbl_eq (s : LSt n d) :
    tagTbl s = s.2.map (fun e => (e.1, e.2.1)) ++
      match s.1 with
      | some c => [(pairW n (List.ofFn c), padFin (2 * n) (wT (List.ofFn c)))]
      | none => [] := rfl

/-- The empty table has no pairs: `keysL [] = []`. -/
theorem keysL_nil : keysL ([] : List (LEntry n)) = [] := by
  rw [keysL_eq, List.map_nil]

/-- The empty lazy state has the empty tag table: `tagTbl (none, []) = []`. -/
theorem tagTbl_none_nil : tagTbl ((none, []) : LSt n d) = [] := by
  rw [tagTbl_eq, List.map_nil, List.nil_append]

end Tables

/-! ### Tags as a table written over a function -/

section Ovr

variable {n d : ℕ}

/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`. -/
theorem ovr_append (A B : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (A ++ B) R = ovr A (ovr B R) := by
  induction A with
  | nil => rw [List.nil_append, ovr_nil]
  | cons e A ih =>
    obtain ⟨p, y⟩ := e
    rw [List.cons_append, ovr_cons, ovr_cons, ih]

/-- The entry at a listed pair has that pair: `p ∈ keysL L → (L.getD ((keysL L).idxOf p) _).1 = p`. -/
theorem getD_idxOf_fst {L : List (LEntry n)} {p : Fin (2 * n) → Bool} (hp : p ∈ keysL L) :
    (L.getD ((keysL L).idxOf p) default).1 = p := by
  induction L with
  | nil => simp [keysL_eq] at hp
  | cons e L ih =>
    rw [keysL_eq, List.map_cons, List.idxOf_cons]
    by_cases h : e.1 = p
    · simp [h]
    · have hp' : p ∈ keysL L := by
        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
        exact hp.resolve_left (Ne.symm h)
      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
      exact ih hp'

/-- **On a listed pair the tag table gives the newest entry's tag:**
`p ∈ keysL L → ovr (L-tags ++ X) R p = (L.getD ((keysL L).idxOf p) _).2.1`. -/
theorem ovr_tags_of_mem (L : List (LEntry n))
    (X : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool)))
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) {p : Fin (2 * n) → Bool}
    (hp : p ∈ keysL L) :
    ovr (L.map (fun e => (e.1, e.2.1)) ++ X) R p = (L.getD ((keysL L).idxOf p) default).2.1 := by
  induction L with
  | nil => simp [keysL_eq] at hp
  | cons e L ih =>
    rw [List.map_cons, List.cons_append, ovr_cons, keysL_eq, List.map_cons, List.idxOf_cons]
    by_cases h : e.1 = p
    · subst h
      simp
    · have hp' : p ∈ keysL L := by
        rw [keysL_eq, List.map_cons, List.mem_cons] at hp
        exact hp.resolve_left (Ne.symm h)
      rw [Function.update_of_ne (Ne.symm h)]
      simp only [show (e.1 == p) = false from beq_false_of_ne h, cond_false, List.getD_cons_succ]
      exact ih hp'

/-- The keys of the tag table: the listed pairs, then the challenge's pair. -/
theorem keys_tagTbl (s : LSt n d) :
    (tagTbl s).map Prod.fst = keysL s.2 ++
      match s.1 with
      | some c => [pairW n (List.ofFn c)]
      | none => [] := by
  rw [tagTbl_eq, List.map_append, List.map_map, keysL_eq]
  congr 1
  cases s.1 <;> rfl

/-- **`tagOf` reads the tag table:** for every `R`, `tagOf s p` is `ovr (tagTbl s) R p` on the keys
of the tag table, and none elsewhere. -/
theorem tagOf_eq_ovr (s : LSt n d) (p : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    tagOf s p = if p ∈ (tagTbl s).map Prod.fst then some (ovr (tagTbl s) R p) else none := by
  rw [tagOf_eq, keys_tagTbl, tagTbl_eq]
  by_cases hp : p ∈ keysL s.2
  · rw [lookL_eq, if_pos hp, if_pos (List.mem_append_left _ hp), ovr_tags_of_mem _ _ _ hp]
  · rw [lookL_eq, if_neg hp, ovr_append, ovr_of_not_mem (by rwa [List.map_map]) _]
    obtain ⟨o, L⟩ := s
    cases o with
    | none => simp [hp]
    | some c =>
      simp only
      by_cases hc : pairW n (List.ofFn c) = p
      · subst hc
        simp [ovr_cons, ovr_nil]
      · simp only [if_neg hc, List.mem_append, hp, List.mem_singleton, false_or]
        rw [if_neg (Ne.symm hc)]

/-- The tag table after an entry: `tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L)`. -/
private theorem tagTbl_cons (o : Option (Fin d → Bool)) (p t : Fin (2 * n) → Bool) (m : List Bool)
    (L : List (LEntry n)) : tagTbl (o, (p, t, m) :: L) = (p, t) :: tagTbl (o, L) := by
  rw [tagTbl_eq, tagTbl_eq, List.map_cons, List.cons_append]

/-- The pairs after an entry: `keysL ((p, t, m) :: L) = p :: keysL L`. -/
private theorem keysL_cons (p t : Fin (2 * n) → Bool) (m : List Bool) (L : List (LEntry n)) :
    keysL ((p, t, m) :: L) = p :: keysL L := by
  rw [keysL_eq, keysL_eq, List.map_cons]

/-- Writing a value the table already gives changes nothing:
`ovr M R p = y → ovr ((p, y) :: M) R = ovr M R`. -/
private theorem ovr_cons_self {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)} {p y : Fin (2 * n) → Bool}
    (h : ovr M R p = y) : ovr ((p, y) :: M) R = ovr M R := by
  rw [ovr_cons, ← h, Function.update_eq_self]

/-- Appending a value at a key changes nothing: `p ∈ keys M → ovr (M ++ [(p, y)]) R = ovr M R`. -/
private theorem ovr_append_of_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {p : Fin (2 * n) → Bool} (hp : p ∈ M.map Prod.fst) (y : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) : ovr (M ++ [(p, y)]) R = ovr M R := by
  rw [ovr_append, ovr_cons, ovr_nil]
  funext x
  by_cases hx : x ∈ M.map Prod.fst
  · exact ovr_of_mem hx _ _
  · rw [ovr_of_not_mem hx, ovr_of_not_mem hx,
      Function.update_of_ne (fun h => hx (by rw [h]; exact hp))]

/-- Appending a value at a new key is writing it first:
`p ∉ keys M → ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R`. -/
private theorem ovr_append_of_not_mem {M : List ((Fin (2 * n) → Bool) × (Fin (2 * n) → Bool))}
    {p : Fin (2 * n) → Bool} (hp : p ∉ M.map Prod.fst) (y : Fin (2 * n) → Bool)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    ovr (M ++ [(p, y)]) R = ovr ((p, y) :: M) R := by
  rw [ovr_append, ovr_cons, ovr_nil, ovr_cons, ovr_update hp]

end Ovr

/-! ### The lazy experiment -/

/-- **XOR twice with the same pad is the identity** (generic; several modules keep a private
copy): `(m ⊕ p) ⊕ p = m` when `|m| ≤ |p|`. -/
theorem zipWith_xor_cancel : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, c :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases c <;> rfl, zipWith_xor_cancel m p (by simpa using h)⟩

section Lazy

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)

/-- **The invariant of the lazy table:** every entry `(p, t, m)` has an `n`-bit message `m` and the
pair `p = r ‖ (m ⊕ f(r))` of some nonce `r`. -/
def LInv {d : ℕ} (s : LSt n d) : Prop :=
  ∀ e ∈ s.2, ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n

/-- `LInv f s` unfolded. -/
theorem lInv_iff {d : ℕ} (s : LSt n d) :
    LInv n f s ↔ ∀ e ∈ s.2,
      ∃ r : Fin n → Bool, e.1 = pairV n (List.ofFn r) (maskL f r e.2.2) ∧ e.2.2.length = n :=
  Iff.rfl

/-- The empty table has the invariant: `LInv f (o, [])`. -/
theorem lInv_nil {d : ℕ} (o : Option (Fin d → Bool)) : LInv n f ((o, []) : LSt n d) :=
  fun _ he => absurd he List.not_mem_nil

/-- **The rejecting decryption answer with the table's tags is the lazy answer:** under the
invariant, `decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w`.

**Proof sketch.** A refused or malformed word gets `⊥` in both. A well-formed word with a listed
pair reads the newest entry `(p, t, m)` at it (`ovr_tags_of_mem`, `getD_idxOf_fst`); its fields are
`r` and `m ⊕ f(r)` (`eq_of_pairV_eq`), so `decL f w = ⟨1, m⟩` (`zipWith_xor_cancel`). A fresh pair is
rejected by both. -/
theorem decAnsW_tagTbl {d : ℕ} (s : LSt n d) (hs : LInv n f s)
    (R : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
    decAnsW f (ovr (tagTbl s) R) true (s.1, keysL s.2) w = lazyDec s w := by
  rw [decAnsW_eq, lazyDec_eq, validW_eq]
  simp only [Bool.not_true, Bool.false_or]
  by_cases hr : refW s.1 w = true
  · simp [hr]
  · rw [Bool.not_eq_true] at hr
    simp only [hr, Bool.not_false, Bool.true_and]
    by_cases hw : wfW n w = true
    · simp only [hw, Bool.true_and]
      have hw' := hw
      rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw'
      by_cases hk : pairW n w ∈ keysL s.2
      · rw [lookL_eq, if_pos hk, tagL_eq, ← pairW_eq, tagTbl_eq, ovr_tags_of_mem _ _ _ hk]
        simp only [decide_eq_true hk, Bool.and_true, decide_eq_true_eq, ↓reduceIte]
        have hfst := getD_idxOf_fst hk
        have hlt : (keysL s.2).idxOf (pairW n w) < s.2.length := by
          have := List.idxOf_lt_length_of_mem hk
          rwa [keysL_eq, List.length_map] at this
        obtain ⟨r, hp, hl⟩ := hs (s.2.getD ((keysL s.2).idxOf (pairW n w)) default) (by
          rw [List.getD_eq_getElem _ _ hlt]
          exact List.getElem_mem hlt)
        by_cases ht : wT w = List.ofFn (s.2.getD ((keysL s.2).idxOf (pairW n w)) default).2.1
        · rw [if_pos ht, if_pos ht.symm, decL_eq]
          obtain ⟨h₁, h₂⟩ := eq_of_pairV_eq hw'.1 hw'.2 List.length_ofFn
            (length_maskL f r hl) ((pairW_eq n w).symm.trans (hfst.symm.trans hp))
          rw [h₁, h₂, padFin_ofFn, maskL_eq, zipWith_xor_cancel _ _ (by
            rw [List.length_ofFn, hl])]
        · rw [if_neg ht, if_neg (Ne.symm ht)]
      · rw [lookL_eq, if_neg hk]
        simp [hk]
    · rw [Bool.not_eq_true] at hw
      simp [hw]

/-- **One step of the lazy experiment** with the nonce `r` and the tape `t` (see the module
docstring). -/
def lazyStep (r : Fin n → Bool) (t : Fin (2 * n) → Bool) :
    ∀ i : Fin 3, (Fin (ins i) → Bool) → LSt n d → (Fin (outs i) → Bool) × LSt n d
  | 0, m, s => (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
        (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
      (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
        (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t, List.ofFn m) :: s.2))
  | 1, w, s => (padFin _ (lazyDec s (List.ofFn w)), s)
  | 2, _, (some c, L) => (padFin _ (List.ofFn c), (some c, L))
  | 2, mm, (none, L) =>
    (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
      (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
        (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
          (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L))

/-- `Enc′` in the lazy experiment: the tag `tagOf s p` or the tape, and a new entry. -/
theorem lazyStep_enc (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (m : Fin (ins 0) → Bool)
    (s : LSt n d) :
    lazyStep ins outs d n f b r t 0 m s =
      (padFin _ (ctW (List.ofFn r) (maskL f r (List.ofFn m))
          (List.ofFn ((tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t))),
        (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
          (tagOf s (pairV n (List.ofFn r) (maskL f r (List.ofFn m)))).getD t,
          List.ofFn m) :: s.2)) := rfl

/-- `Dec′` in the lazy experiment answers `lazyDec`. -/
theorem lazyStep_dec (r : Fin n → Bool) (t : Fin (2 * n) → Bool) (w : Fin (ins 1) → Bool)
    (s : LSt n d) :
    lazyStep ins outs d n f b r t 1 w s = (padFin _ (lazyDec s (List.ofFn w)), s) := rfl

/-- A repeated challenge in the lazy experiment. -/
theorem lazyStep_challenge_some (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
    (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) (L : List (LEntry n)) :
    lazyStep ins outs d n f b r t 2 mm (some c, L) = (padFin _ (List.ofFn c), (some c, L)) := rfl

/-- The first challenge in the lazy experiment. -/
theorem lazyStep_challenge_none (r : Fin n → Bool) (t : Fin (2 * n) → Bool)
    (mm : Fin (ins 2) → Bool) (L : List (LEntry n)) :
    lazyStep ins outs d n f b r t 2 mm (none, L) =
      (padFin _ (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t))),
        (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
          (List.ofFn ((tagOf ((none, L) : LSt n d) (pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))).getD t)))), L)) := rfl

/-- One call of the lazy experiment with the tape `t`: draw the nonce and take `lazyStep`. -/
noncomputable def ettLazyK (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d)
    (t : Fin (2 * n) → Bool) : ProbComp ((Fin (outs i) → Bool) × LSt n d) :=
  (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s)

/-- `ettLazyK … i x s t = (sample (Fin n → Bool)).bind fun r => pure (lazyStep … r t i x s)`. -/
theorem ettLazyK_eq (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) (t : Fin (2 * n) → Bool) :
    ettLazyK ins outs d n f b i x s t =
      (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := rfl

/-- **The lazy experiment:** one fresh tape per query (`freshImpl`). -/
noncomputable def ettLazy : QueryImpl (bitSpec ins outs) (LSt n d) unifSpec :=
  freshImpl (ettLazyK ins outs d n f b)

/-- `ettLazy … = freshImpl (ettLazyK …)`. -/
theorem ettLazy_eq : ettLazy ins outs d n f b = freshImpl (ettLazyK ins outs d n f b) := rfl

/-- **The lazy experiment with tapes in advance** (`tapeImpl`). -/
noncomputable def ettLazyTape (T : ℕ → Fin (2 * n) → Bool) : QueryImpl (bitSpec ins outs) (LSt n d × ℕ) unifSpec :=
  tapeImpl (ettLazyK ins outs d n f b) T

/-- `ettLazyTape … T = tapeImpl (ettLazyK …) T`. -/
theorem ettLazyTape_eq (T : ℕ → Fin (2 * n) → Bool) :
    ettLazyTape ins outs d n f b T = tapeImpl (ettLazyK ins outs d n f b) T := rfl

/-- **Tapes in advance have the law of fresh tapes** (`expect_simulate_tapeImpl`). -/
theorem expect_ettLazyTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : LSt n d) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → Fin (2 * n) → Bool))
        (fun T => expect (simulate (ettLazyTape ins outs d n f b (AdaptiveCPA.extTape T)) c (s, j))
          fun p => G p.1) =
      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 :=
  expect_simulate_tapeImpl _ κ G c m hc s j hj

end Lazy

/-! ### The law of the lazy experiment -/

section LazyLaw

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (b : Bool)

/-- One call of the lazy experiment: draw the tape, then the nonce, and take `lazyStep`. -/
theorem ettLazy_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : LSt n d) :
    ettLazy ins outs d n f b i x s =
      (sample (Fin (2 * n) → Bool)).bind fun t =>
        (sample (Fin n → Bool)).bind fun r => .pure (lazyStep ins outs d n f b r t i x s) := by
  rw [ettLazy_eq, freshImpl_apply]
  rfl

/-- **The rejecting experiment with a uniform random tag function is the lazy experiment**
[PS10, Thm 170.4, proof]: for `(6n + 4)`-bit records, `n`-bit messages and `2n`-bit challenge
queries, from a lazy state with the invariant `LInv`, averaging over `R` with the table's tags
written over it, `𝔼_R 𝔼[G (simulate (ettImpl … (ovr (tagTbl s) R) true b) c (s.1, keysL s.2))] =
𝔼[G (simulate (ettLazy …) c s)]`.

**Proof sketch.** Induction on `c`; both sides draw a nonce per query (exchanged with the
average, `expect_sample_comm`). An encryption or a first challenge at a pair of the tag table reads
the table (`tagOf_eq_ovr`, `ovr_of_mem`), and the new entry repeats it (`ovr_cons_self`,
`ovr_append_of_mem`); at a new pair it reads `R` there, moved into the table by
`expect_sample_ovr` and matched by the lazy tape (`ovr_append_of_not_mem`). Decryption answers agree
(`decAnsW_tagTbl`). A repeated challenge reads nothing. -/
theorem expect_ettImpl_lazy (hd : d = 6 * n + 4) (hi0 : ins 0 = n) (hi2 : ins 2 = n + n)
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : LSt n d)
    (hs : LInv n f s) :
    expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)))
        (fun R => expect (simulate (ettImpl ins outs d n f (ovr (tagTbl s) R) true b) c
          (s.1, keysL s.2)) fun p => G p.1) =
      expect (simulate (ettLazy ins outs d n f b) c s) fun p => G p.1 := by
  induction c generalizing s with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    rw [simulate_query, ettLazy_apply]
    simp only [simulate_query, ettImpl_apply, OracleComp.bind_assoc, OracleComp.pure_bind,
      expect_bind]
    rw [expect_sample_comm (α := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
      expect_sample_comm (α := Fin (2 * n) → Bool)]
    refine congrArg _ (funext fun r => ?_)
    match i, x, k, ih with
    | 0, m, k, ih =>
      have hm : (List.ofFn m).length = n := by rw [List.length_ofFn, hi0]
      simp only [ettStep_enc, lazyStep_enc, encW_eq_ctW]
      by_cases hp : pairV n (List.ofFn r) (maskL f r (List.ofFn m)) ∈ (tagTbl s).map Prod.fst
      · -- the pair has a tag already
        have hy : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_mem hp R _
        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
          if_pos hp]
        simp only [Option.getD_some, hy, expect_const]
        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)),
            ovr (tagTbl s) (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m)))
              (pairV n (List.ofFn r) (maskL f r (List.ofFn m))), List.ofFn m) :: s.2) := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨r, rfl, hm⟩
          · exact hs e he
        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
        refine congrArg _ (funext fun R => ?_)
        rw [ovr_cons_self (hy R)]
      · -- a new pair: its tag is the tape
        rw [tagOf_eq_ovr s _ (fun _ => pairV n (List.ofFn r) (maskL f r (List.ofFn m))),
          if_neg hp]
        simp only [Option.getD_none]
        have e : ∀ R, ovr (tagTbl s) R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) =
            R (pairV n (List.ofFn r) (maskL f r (List.ofFn m))) := fun R => ovr_of_not_mem hp R
        simp only [e]
        rw [expect_sample_ovr (tagTbl s) hp (fun t g => expect (simulate
          (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
            (maskL f r (List.ofFn m)) (List.ofFn t))))
          (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: keysL s.2)) fun p => G p.1)]
        refine congrArg _ (funext fun t => ?_)
        have hs' : LInv n f (s.1, (pairV n (List.ofFn r) (maskL f r (List.ofFn m)), t,
            List.ofFn m) :: s.2) := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨r, rfl, hm⟩
          · exact hs e he
        rw [← ih _ _ hs', tagTbl_cons, keysL_cons, Prod.mk.eta]
    | 1, w, k, ih =>
      simp only [ettStep_dec, lazyStep_dec, decAnsW_tagTbl n f s hs, expect_const]
      exact ih _ s hs
    | 2, mm, k, ih =>
      obtain ⟨o, L⟩ := s
      cases o with
      | some c =>
        simp only [ettStep_challenge_some, lazyStep_challenge_some, expect_const]
        exact ih _ (some c, L) hs
      | none =>
        have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
          rw [AdaptiveCPA.msgOf_eq]
          cases b <;> simp [this]
        have hl := length_maskL f r hmsg
        have hrec : ∀ t : Fin (2 * n) → Bool,
            List.ofFn (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
              (List.ofFn mm))) (List.ofFn t))) =
            ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t) := by
          intro t
          refine ofFn_padFin_of_length ?_
          rw [ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn, hl, List.length_ofFn,
            hd]
          omega
        have htbl : ∀ t : Fin (2 * n) → Bool,
            tagTbl ((some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
              (List.ofFn mm))) (List.ofFn t))), L) : LSt n d) =
            tagTbl ((none, L) : LSt n d) ++ [(pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))), t)] := by
          intro t
          rw [tagTbl_eq, tagTbl_eq, List.append_nil]
          simp only
          rw [hrec, pairW_eq, wR_ctW, wC_ctW, wT_ctW, padFin_ofFn]
        simp only [ettStep_challenge_none, lazyStep_challenge_none, encW_eq_ctW]
        by_cases hp : pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) ∈
            (tagTbl ((none, L) : LSt n d)).map Prod.fst
        · have hy : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
              ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n (List.ofFn r)
                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) (pairV n (List.ofFn r)
                (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) := fun R => ovr_of_mem hp R _
          rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_pos hp]
          simp only [Option.getD_some, hy, expect_const]
          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn (ovr (tagTbl ((none, L) : LSt n d)) (fun _ => pairV n
              (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))))
              (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))))))), L) hs,
            htbl]
          refine congrArg _ (funext fun R => ?_)
          rw [ovr_append_of_mem hp]
        · rw [tagOf_eq_ovr _ _ (fun _ => pairV n (List.ofFn r)
            (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), if_neg hp]
          simp only [Option.getD_none]
          have e : ∀ R, ovr (tagTbl ((none, L) : LSt n d)) R (pairV n (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) =
              R (pairV n (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))) :=
            fun R => ovr_of_not_mem hp R
          simp only [e]
          rw [expect_sample_ovr (tagTbl ((none, L) : LSt n d)) hp (fun t g => expect (simulate
            (ettImpl ins outs d n f g true b) (k (padFin _ (ctW (List.ofFn r)
              (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm))) (List.ofFn t))))
            (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b (List.ofFn mm)))
              (List.ofFn t))), keysL L)) fun p => G p.1)]
          refine congrArg _ (funext fun t => ?_)
          rw [← ih _ (some (padFin d (ctW (List.ofFn r) (maskL f r (AdaptiveCPA.msgOf n b
            (List.ofFn mm))) (List.ofFn t))), L) hs, htbl]
          refine congrArg _ (funext fun R => ?_)
          rw [ovr_append_of_not_mem hp]

end LazyLaw

end TCSlib.Cryptography.Composability.ETTGame
