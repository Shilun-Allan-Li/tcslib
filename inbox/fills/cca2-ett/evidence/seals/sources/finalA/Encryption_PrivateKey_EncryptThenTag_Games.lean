/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Foundations.BitLists
/- DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Games: whole-file closure seal of `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean` (PolyExpr.eval open). -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
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
  Lean.logInfo m!"DLC-SEAL Encryption_PrivateKey_EncryptThenTag_Games: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CCA2 games of the encrypt-then-tag scheme with a pad and a tag function

The scheme of [PS10, Algorithm 169.3] encrypts `m` as `⟨r, ⟨c₁, t⟩⟩` with a fresh `n`-bit nonce
`r`, the mask `c₁ = m ⊕ f(r)` and the tag `t = g(r ‖ c₁)`, where `f = f_{k₁}` and `g = f_{k₂}` are the
keyed functions at parameters `n` and `2n`. The proof of [PS10, Theorem 170.4] replaces them by
other functions; this file states the CCA2 experiment's oracles with `f` and `g` arbitrary, on
bit-string oracles of arbitrary lengths (`bitSpec ins outs`; oracle `0` is `Enc`, `1` is `Dec`,
`2` is `Challenge`), with the challenge recorded at width `d`.

**The state** (`St n d`) is the recorded challenge and the list of pairs `r ‖ c₁` of the earlier
`Enc` answers. **Every query draws one nonce** `r`, used by `Enc` and by a first challenge only
(`ettImpl`); the answer is then a deterministic function of the nonce (`ettStep`).

* `Enc` on `m` answers `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩` and adds the pair `r ‖ c₁` to the list.
* `Dec` on `w` refuses the recorded challenge; otherwise it parses `w = ⟨r, ⟨c₁, t⟩⟩` with the total
  projections (`wR`, `wC`, `wT`), and answers `⟨1, c₁ ⊕ f(r)⟩` when `r` and `c₁` have `n` bits and
  `t = g(r ‖ c₁)` (`validW`), else `⊥`. With `rej = true` it also rejects a pair that is not in
  the list (**fresh pairs are rejected**).
* `Challenge` on `⟨m₀, m₁⟩` encrypts `m_b` once and records it; later it repeats the record.

The bad flag of the comparison between `rej = false` and `rej = true` (`ettBad`) records a `Dec`
query that is not refused, has a valid tag and a fresh pair (`hitW`). The nonces drawn in advance
from tapes give `ettTape`, the experiment run by the PRF reduction.

## Main definitions

* `ETTGame.encW`, `wR`, `wC`, `wT`, `validW`, `decL`, `pairW`: ciphertext words.
* `ETTGame.St`, `ettStep`, `ettImpl`, `ettBad`, `ettTape`: the experiments.
* `ETTGame.ettAcc`: a machine's acceptance probability in the experiment.

## Main results

* `ETTGame.ettStep_enc`, `_dec`, `_challenge_some`, `_challenge_none`: the answers.
* `ETTGame.encW_eq_ctW`: an encryption reads the tag function at its pair only.
* `ETTGame.length_encW`, `ETTGame.eq_ctW_of_wfW`: ciphertext lengths and canonical parsing.
* `ETTGame.expect_ettTape`: nonces in advance have the law of fresh nonces.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Ciphertext words -/

section Words

variable {n : ℕ}

/-- The pair `r ‖ c₁` read as a `2n`-bit vector. -/
def pairV (n : ℕ) (r c : List Bool) : Fin (2 * n) → Bool := padFin (2 * n) (r ++ c)

/-- `pairV n r c = padFin (2n) (r ++ c)`. -/
theorem pairV_eq (n : ℕ) (r c : List Bool) : pairV n r c = padFin (2 * n) (r ++ c) := rfl

/-- The tag `⟦g (r ‖ c₁)⟧`. -/
def tagL (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) : List Bool :=
  List.ofFn (g (pairV n r c))

/-- `tagL g r c = ⟦g (pairV n r c)⟧`. -/
theorem tagL_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r c : List Bool) :
    tagL g r c = List.ofFn (g (pairV n r c)) := rfl

/-- The ciphertext word `⟨r, ⟨c₁, t⟩⟩`. -/
def ctW (r c t : List Bool) : List Bool := pairEncode r (pairEncode c t)

/-- `ctW r c t = ⟨r, ⟨c, t⟩⟩`. -/
theorem ctW_eq (r c t : List Bool) : ctW r c t = pairEncode r (pairEncode c t) := rfl

/-- The mask `c₁ = m ⊕ ⟦f r⟧`. -/
def maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) : List Bool :=
  List.zipWith xor m (List.ofFn (f r))

/-- `maskL f r m = m ⊕ ⟦f r⟧`. -/
theorem maskL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) (m : List Bool) :
    maskL f r m = List.zipWith xor m (List.ofFn (f r)) := rfl

/-- **The encryption** of the message list `m` with the nonce `r`:
`⟨r, ⟨c₁, ⟦g (r ‖ c₁)⟧⟩⟩` with `c₁ = maskL f r m`. -/
def encW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (r : Fin n → Bool) (m : List Bool) : List Bool :=
  ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m))

/-- `encW f g r m = ctW ⟦r⟧ c₁ (tagL g ⟦r⟧ c₁)` with `c₁ = maskL f r m`. -/
theorem encW_eq (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
    encW f g r m = ctW (List.ofFn r) (maskL f r m) (tagL g (List.ofFn r) (maskL f r m)) := rfl

/-- **An encryption reads the tag function at its pair only:**
`encW f g r m = ctW ⟦r⟧ c₁ ⟦g (pairV n ⟦r⟧ c₁)⟧` with `c₁ = maskL f r m`. -/
theorem encW_eq_ctW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) (m : List Bool) :
    encW f g r m = ctW (List.ofFn r) (maskL f r m)
      (List.ofFn (g (pairV n (List.ofFn r) (maskL f r m)))) := by
  rw [encW_eq, tagL_eq]

/-- The nonce field of a word: `wR w = pairFstD w`. -/
def wR (w : List Bool) : List Bool := pairFstD w

/-- The mask field of a word: `wC w = pairFstD (pairSndD w)`. -/
def wC (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The tag field of a word: `wT w = pairSndD (pairSndD w)`. -/
def wT (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- `wR w = pairFstD w`. -/
theorem wR_eq (w : List Bool) : wR w = pairFstD w := rfl

/-- `wC w = pairFstD (pairSndD w)`. -/
theorem wC_eq (w : List Bool) : wC w = pairFstD (pairSndD w) := rfl

/-- `wT w = pairSndD (pairSndD w)`. -/
theorem wT_eq (w : List Bool) : wT w = pairSndD (pairSndD w) := rfl

/-- The fields of a ciphertext word: `wR (ctW r c t) = r`. -/
theorem wR_ctW (r c t : List Bool) : wR (ctW r c t) = r := by
  rw [wR_eq, ctW_eq, pairFstD_pairEncode]

/-- The fields of a ciphertext word: `wC (ctW r c t) = c`. -/
theorem wC_ctW (r c t : List Bool) : wC (ctW r c t) = c := by
  rw [wC_eq, ctW_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The fields of a ciphertext word: `wT (ctW r c t) = t`. -/
theorem wT_ctW (r c t : List Bool) : wT (ctW r c t) = t := by
  rw [wT_eq, ctW_eq, pairSndD_pairEncode, pairSndD_pairEncode]

/-- **Well-formedness:** the nonce and the mask fields have `n` bits,
`wfW n w = (|wR w| = n && |wC w| = n)`. -/
def wfW (n : ℕ) (w : List Bool) : Bool :=
  decide ((wR w).length = n) && decide ((wC w).length = n)

/-- `wfW n w = (decide (|wR w| = n) && decide (|wC w| = n))`. -/
theorem wfW_eq (n : ℕ) (w : List Bool) :
    wfW n w = (decide ((wR w).length = n) && decide ((wC w).length = n)) := rfl

/-- **A valid word:** well formed, with the tag `wT w = tagL g (wR w) (wC w)`. -/
def validW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) : Bool :=
  wfW n w && decide (wT w = tagL g (wR w) (wC w))

/-- `validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w)))`. -/
theorem validW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (w : List Bool) :
    validW g w = (wfW n w && decide (wT w = tagL g (wR w) (wC w))) := rfl

/-- **The decryption** of a word: `⟨1, wC w ⊕ ⟦f (wR w)⟧⟩`. -/
def decL (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) : List Bool :=
  true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w))))

/-- `decL f w = true :: (wC w ⊕ ⟦f (padFin n (wR w))⟧)`. -/
theorem decL_eq (f : (Fin n → Bool) → (Fin n → Bool)) (w : List Bool) :
    decL f w = true :: List.zipWith xor (wC w) (List.ofFn (f (padFin n (wR w)))) := rfl

/-- The pair of a word, as a `2n`-bit vector: `pairW n w = pairV n (wR w) (wC w)`. -/
def pairW (n : ℕ) (w : List Bool) : Fin (2 * n) → Bool := pairV n (wR w) (wC w)

/-- `pairW n w = pairV n (wR w) (wC w)`. -/
theorem pairW_eq (n : ℕ) (w : List Bool) : pairW n w = pairV n (wR w) (wC w) := rfl

/-- The mask of an `n`-bit message has `n` bits. -/
theorem length_maskL (f : (Fin n → Bool) → (Fin n → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : (maskL f r m).length = n := by
  rw [maskL_eq, List.length_zipWith, List.length_ofFn, hm, Nat.min_self]

/-- **The ciphertext length:** an encryption of an `n`-bit message has `6n + 4` bits. -/
theorem length_encW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : (encW f g r m).length = 6 * n + 4 := by
  rw [encW_eq, ctW_eq, length_pairEncode, length_pairEncode, List.length_ofFn,
    length_maskL f r hm, tagL_eq, List.length_ofFn]
  omega

/-- **Canonical parsing:** for `n > 0`, a well-formed word is the ciphertext word of its fields,
`w = ctW (wR w) (wC w) (wT w)` (`eq_pairEncode_of_pairFstD_ne`, the nonempty fields). -/
theorem eq_ctW_of_wfW {w : List Bool} (hn : 0 < n) (hw : wfW n w = true) :
    w = ctW (wR w) (wC w) (wT w) := by
  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
  have h₁ : pairFstD w ≠ [] := by
    intro h
    have := hw.1
    rw [wR_eq, h, List.length_nil] at this
    omega
  have h₂ : pairFstD (pairSndD w) ≠ [] := by
    intro h
    have := hw.2
    rw [wC_eq, h, List.length_nil] at this
    omega
  rw [ctW_eq, wR_eq, wC_eq, wT_eq, ← eq_pairEncode_of_pairFstD_ne h₂]
  exact eq_pairEncode_of_pairFstD_ne h₁

/-- An encryption is well formed: `wfW n (encW f g r m)` for an `n`-bit `m`. -/
theorem wfW_encW (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (r : Fin n → Bool) {m : List Bool}
    (hm : m.length = n) : wfW n (encW f g r m) = true := by
  rw [wfW_eq, encW_eq, wR_ctW, wC_ctW, List.length_ofFn, length_maskL f r hm]
  simp

/-- **Pairs of `n`-bit fields determine the fields:** if `|r| = |c| = |r'| = |c'| = n` and
`pairV n r c = pairV n r' c'`, then `r = r'` and `c = c'`. -/
theorem eq_of_pairV_eq {r c r' c' : List Bool} (hr : r.length = n) (hc : c.length = n)
    (hr' : r'.length = n) (hc' : c'.length = n) (h : pairV n r c = pairV n r' c') :
    r = r' ∧ c = c' := by
  have h1 : r ++ c = r' ++ c' := by
    have e : List.ofFn (pairV n r c) = List.ofFn (pairV n r' c') := by rw [h]
    rw [pairV_eq, pairV_eq, ofFn_padFin_of_length (by rw [List.length_append, hr, hc]; omega),
      ofFn_padFin_of_length (by rw [List.length_append, hr', hc']; omega)] at e
    exact e
  exact List.append_inj h1 (hr.trans hr'.symm)

end Words

/-! ### The state and the decryption answer -/

section State

variable {n d : ℕ}

/-- **The state of the experiment:** the recorded challenge and the pairs of the `Enc` answers. -/
abbrev St (n d : ℕ) : Type := Option (Fin d → Bool) × List (Fin (2 * n) → Bool)

/-- `St n d = Option (Fin d → Bool) × List (Fin (2n) → Bool)`. -/
theorem St_eq (n d : ℕ) : St n d = (Option (Fin d → Bool) × List (Fin (2 * n) → Bool)) := rfl

/-- **The refusal test:** the word `w` is the recorded challenge,
`refW (some c) w = (⟦c⟧ = w)`, `refW none w = false`. -/
def refW (o : Option (Fin d → Bool)) (w : List Bool) : Bool :=
  match o with
  | some c => decide (List.ofFn c = w)
  | none => false

/-- `refW none w = false`. -/
theorem refW_none (w : List Bool) : refW (none : Option (Fin d → Bool)) w = false := rfl

/-- `refW (some c) w = decide (⟦c⟧ = w)`. -/
theorem refW_some (c : Fin d → Bool) (w : List Bool) : refW (some c) w = decide (List.ofFn c = w) :=
  rfl

/-- **The decryption answer** in state `s`, with fresh pairs rejected when `rej` holds: `decL f w`
if `w` is not refused, valid, and (when `rej`) its pair is in the list; else `[]` (read as `⊥`). -/
def decAnsW (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (rej : Bool) (s : St n d) (w : List Bool) : List Bool :=
  if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w else []

/-- `decAnsW f g rej s w = if !refW s.1 w && validW g w && (!rej || pairW n w ∈ s.2) then decL f w
else []`. -/
theorem decAnsW_eq (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej : Bool) (s : St n d) (w : List Bool) :
    decAnsW f g rej s w =
      if (!refW s.1 w && validW g w && (!rej || decide (pairW n w ∈ s.2))) = true then decL f w
      else [] := rfl

/-- **The bad event of a decryption query:** not refused, valid, and a fresh pair. -/
def hitW (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) : Bool :=
  !refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)

/-- `hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2))`. -/
theorem hitW_eq (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool) :
    hitW g s w = (!refW s.1 w && validW g w && !decide (pairW n w ∈ s.2)) := rfl

/-- **Off the bad event the two decryption answers agree:** `hitW g s w = false →
decAnsW f g false s w = decAnsW f g true s w`. -/
theorem decAnsW_agree (f : (Fin n → Bool) → (Fin n → Bool))
    (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (s : St n d) (w : List Bool)
    (h : hitW g s w = false) : decAnsW f g false s w = decAnsW f g true s w := by
  rw [decAnsW_eq, decAnsW_eq]
  rw [hitW_eq] at h
  cases hr : refW s.1 w <;> cases hv : validW g w <;>
    cases hm : decide (pairW n w ∈ s.2) <;> simp_all

end State

/-! ### The experiments -/

section Experiments

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
  (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (rej b : Bool)

/-- **One step of the experiment with the nonce `r`** (see the module docstring). -/
def ettStep (r : Fin n → Bool) :
    ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → (Fin (outs i) → Bool) × St n d
  | 0, m, s => (padFin _ (encW f g r (List.ofFn m)),
      (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2))
  | 1, w, s => (padFin _ (decAnsW f g rej s (List.ofFn w)), s)
  | 2, _, (some c, T) => (padFin _ (List.ofFn c), (some c, T))
  | 2, mm, (none, T) => (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
      (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T))

/-- `Enc` on `m` answers `encW f g r m` and adds the pair `r ‖ maskL f r m` to the list. -/
theorem ettStep_enc (r : Fin n → Bool) (m : Fin (ins 0) → Bool) (s : St n d) :
    ettStep ins outs d n f g rej b r 0 m s =
      (padFin _ (encW f g r (List.ofFn m)),
        (s.1, pairV n (List.ofFn r) (maskL f r (List.ofFn m)) :: s.2)) := rfl

/-- `Dec` on `w` answers `decAnsW f g rej s w` and keeps the state. -/
theorem ettStep_dec (r : Fin n → Bool) (w : Fin (ins 1) → Bool) (s : St n d) :
    ettStep ins outs d n f g rej b r 1 w s = (padFin _ (decAnsW f g rej s (List.ofFn w)), s) := rfl

/-- A later challenge repeats the record and keeps the state. -/
theorem ettStep_challenge_some (r : Fin n → Bool) (mm : Fin (ins 2) → Bool) (c : Fin d → Bool)
    (T : List (Fin (2 * n) → Bool)) :
    ettStep ins outs d n f g rej b r 2 mm (some c, T) = (padFin _ (List.ofFn c), (some c, T)) := rfl

/-- The first challenge encrypts `m_b` with the nonce `r` and records it. -/
theorem ettStep_challenge_none (r : Fin n → Bool) (mm : Fin (ins 2) → Bool)
    (T : List (Fin (2 * n) → Bool)) :
    ettStep ins outs d n f g rej b r 2 mm (none, T) =
      (padFin _ (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm))),
        (some (padFin d (encW f g r (AdaptiveCPA.msgOf n b (List.ofFn mm)))), T)) := rfl

/-- **The experiment with pad function `f` and tag function `g`:** every query draws a nonce `r`
and takes one `ettStep`. -/
noncomputable def ettImpl : QueryImpl (bitSpec ins outs) (St n d) unifSpec :=
  fun i x s => (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s)

/-- `ettImpl … i x s = (sample (Fin n → Bool)).bind fun r => pure (ettStep … r i x s)`. -/
theorem ettImpl_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d) :
    ettImpl ins outs d n f g rej b i x s =
      (sample (Fin n → Bool)).bind fun r => .pure (ettStep ins outs d n f g rej b r i x s) := rfl

/-- The experiment draws one coin per query (`freshImpl`). -/
theorem ettImpl_eq_freshImpl :
    ettImpl ins outs d n f g rej b =
      freshImpl fun i x s r => .pure (ettStep ins outs d n f g rej b r i x s) := by
  funext i x s
  rw [ettImpl_apply, freshImpl_apply]

/-- The bad event of a query: a decryption query with `hitW`. -/
def hitQ : ∀ i : Fin 3, (Fin (ins i) → Bool) → St n d → Bool
  | 0, _, _ => false
  | 1, w, s => hitW g s (List.ofFn w)
  | 2, _, _ => false

/-- An encryption query never raises the bad flag. -/
theorem hitQ_zero (m : Fin (ins 0) → Bool) (s : St n d) : hitQ ins d n g 0 m s = false := rfl

/-- A decryption query raises the bad flag by `hitW`. -/
theorem hitQ_one (w : Fin (ins 1) → Bool) (s : St n d) :
    hitQ ins d n g 1 w s = hitW g s (List.ofFn w) := rfl

/-- A challenge query never raises the bad flag. -/
theorem hitQ_two (mm : Fin (ins 2) → Bool) (s : St n d) : hitQ ins d n g 2 mm s = false := rfl

/-- **The experiment with the bad flag:** `ettImpl`, and the flag raised by `hitQ`. -/
noncomputable def ettBad : QueryImpl (bitSpec ins outs) (St n d × Bool) unifSpec :=
  fun i x s => (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
    .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1))

/-- `ettBad … i x s = (ettImpl … i x s.1).bind fun p => pure (p.1, (p.2, s.2 || hitQ … i x s.1))`. -/
theorem ettBad_apply (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d × Bool) :
    ettBad ins outs d n f g rej b i x s =
      (ettImpl ins outs d n f g rej b i x s.1).bind fun p =>
        .pure (p.1, (p.2, s.2 || hitQ ins d n g i x s.1)) := rfl

/-- **The experiment with nonces in advance** (`rej = false`): the `j`-th query uses the nonce
`T j` (`tapeImpl`). -/
def ettTape (T : ℕ → Fin n → Bool) : QueryImpl (bitSpec ins outs) (St n d × ℕ) unifSpec :=
  tapeImpl (fun i x s r => .pure (ettStep ins outs d n f g false b r i x s)) T

/-- `ettTape … T i x (s, j) = pure (ettStep … false b (T j) i x s)` with the counter advanced. -/
theorem ettTape_apply (T : ℕ → Fin n → Bool) (i : Fin 3) (x : Fin (ins i) → Bool) (s : St n d)
    (j : ℕ) :
    ettTape ins outs d n f g b T i x (s, j) =
      .pure ((ettStep ins outs d n f g false b (T j) i x s).1,
        ((ettStep ins outs d n f g false b (T j) i x s).2, j + 1)) := by
  rw [ettTape, tapeImpl_apply, OracleComp.pure_bind]

/-- **Nonces in advance have the law of fresh nonces:** for a computation with at most `m`
queries and `j + m ≤ κ`,
`𝔼_{T ← ({0,1}^n)^κ} 𝔼[G (simulate (ettTape (extTape T)) c (s, j))] =
𝔼[G (simulate (ettImpl … false b) c s)]` (`expect_simulate_tapeImpl`). -/
theorem expect_ettTape (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : St n d) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → Fin n → Bool))
        (fun T => expect (simulate (ettTape ins outs d n f g b (AdaptiveCPA.extTape T)) c (s, j))
          fun p => G p.1) =
      expect (simulate (ettImpl ins outs d n f g false b) c s) fun p => G p.1 := by
  rw [ettImpl_eq_freshImpl]
  exact expect_simulate_tapeImpl _ κ G c m hc s j hj

/-- **The experiment along equal lengths:** for `ins = ins'`, `outs = outs'` and `d = d'`, the
expected first output bit of a machine's run against `ettImpl` agrees. -/
theorem expect_ettImpl_transport {ins ins' outs outs' : Fin 3 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (ettImpl ins' outs' d' n f g rej b) (A.toComp (bitCodec ins' outs' 1) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hi ho hd
  rfl

/-- **The acceptance probability of a machine** in the experiment with `f` and `g`, averaged over
its coins: `𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f g rej b) (A.toComp … r) (none, [])]`. -/
noncomputable def ettAcc (A : NUPPT) (Q : ℕ) : ℝ :=
  expect (sample (A.Coins n)) fun r =>
    expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
      (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)

/-- `ettAcc … A Q = 𝔼_r 𝔼[⟦output⟧₀ = 1 | simulate (ettImpl …) (A.toComp … r) (none, [])]`. -/
theorem ettAcc_eq (A : NUPPT) (Q : ℕ) :
    ettAcc ins outs d n f g rej b A Q =
      expect (sample (A.Coins n)) fun r =>
        expect (simulate (ettImpl ins outs d n f g rej b) (A.toComp (bitCodec ins outs 1) n Q r)
          (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) :=
  rfl

/-- The acceptance probability lies in `[0, 1]`. -/
theorem ettAcc_nonneg (A : NUPPT) (Q : ℕ) : 0 ≤ ettAcc ins outs d n f g rej b A Q := by
  rw [ettAcc_eq]
  refine expect_nonneg _ fun r => expect_nonneg _ fun p => ?_
  split <;> norm_num

/-- The acceptance probability lies in `[0, 1]`. -/
theorem ettAcc_le_one (A : NUPPT) (Q : ℕ) : ettAcc ins outs d n f g rej b A Q ≤ 1 := by
  rw [ettAcc_eq]
  refine (expect_mono _ fun r => ?_).trans (le_of_eq (expect_const _ 1))
  refine (expect_mono _ fun p => ?_).trans (le_of_eq (expect_const _ 1))
  split <;> norm_num

end Experiments

end TCSlib.Cryptography.Composability.ETTGame
