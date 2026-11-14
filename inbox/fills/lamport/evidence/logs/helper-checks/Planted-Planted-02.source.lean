/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The fixed-position Lamport planting coupling

## Main definitions

* `plantTable` replaces one preimage in a typed Lamport key table.
* `tableSignature` selects one preimage per message bit.
* `plantedPublic` replaces one image without reading its preimage.
* `firstQuery` and `Safe` record whether the sole query avoids the planted cell.
* `abortingImpl` answers safe queries and remembers an unsafe query.

## Main results

* `planted_coupling`: on the safe branch of a computation with at most one query,
  the planted implementation returns the honest output and never aborts.
* `extract_planted`: an accepting signature with the planted message bit inverts
  the planted image.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 137.1 and Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography TCSlib.Cryptography.Games
open Complexity Turing

/-- A table has an `n`-bit preimage at each coordinate `(i,c)`. -/
abbrev Table (n : ℕ) := (Fin n × Bool) → Fin n → Bool

/-- The type of tables is the function type `(Fin n × Bool) → Fin n → Bool`. -/
theorem Table_eq (n : ℕ) : Table n = ((Fin n × Bool) → Fin n → Bool) := rfl

/-- Serialize a public table as the tuple of its pairs of images. -/
def publicWord {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
    pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true))))

/-- The public word is the tuple of the encoded pairs `⟨Y(i,0),Y(i,1)⟩`. -/
theorem publicWord_eq {n ℓ : ℕ} (Y : (Fin n × Bool) → Fin ℓ → Bool) :
    publicWord Y = PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
      pairEncode (List.ofFn (Y (i, false))) (List.ofFn (Y (i, true)))) := rfl

/-- Serialize a preimage table in row order, with its false and true cells adjacent. -/
def secretWord {n : ℕ} (T : Table n) : List Bool :=
  (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten

/-- The secret word concatenates `T(i,0) ‖ T(i,1)` for consecutive rows `i`. -/
theorem secretWord_eq {n : ℕ} (T : Table n) :
    secretWord T =
      (List.ofFn fun i : Fin n => List.ofFn (T (i, false)) ++ List.ofFn (T (i, true))).flatten :=
  rfl

/-- A serialized table contains `n` rows of `2n` bits, hence `2n²` bits. -/
theorem length_secretWord {n : ℕ} (T : Table n) : (secretWord T).length = 2 * n * n := by
  simp only [secretWord, List.length_flatten, List.map_ofFn, Function.comp_apply, List.length_append,
    List.length_ofFn, List.ofFn_const, List.sum_replicate, nsmul_eq_mul]
  ring

/-- Replace preimage `(i,c)` by `x`, leaving every other cell unchanged. -/
def plantTable {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (p : Fin n × Bool) : Fin n → Bool :=
  if p = (i, c) then x else T p

/-- Planting returns `x` at the selected cell and `T p` elsewhere. -/
theorem plantTable_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (p : Fin n × Bool) :
    plantTable T i c x p = if p = (i, c) then x else T p := rfl

/-- The planted cell contains `x`. -/
theorem plantTable_at {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    plantTable T i c x (i, c) = x := by
  simp only [plantTable, if_true]

/-- A cell different from `(i,c)` retains its original preimage. -/
theorem plantTable_ne {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    {p : Fin n × Bool} (hp : p ≠ (i, c)) : plantTable T i c x p = T p := by
  rw [plantTable_eq, if_neg hp]

/-- Planting a table is the ordinary update of its selected coordinate. -/
theorem plantTable_update {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) : plantTable T i c x = Function.update T (i, c) x := by
  funext p
  rw [plantTable_eq, Function.update_apply]

/-- The signature is the flattened table of preimages selected by the message bits. -/
def tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) : Fin (n * n) → Bool :=
  fun j => T ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm j).2

/-- At the flattened index for `(i,k)`, the signature reads bit `k` of `T(i,m i)`. -/
theorem tableSignature_apply {n : ℕ} (T : Table n) (m : Fin n → Bool)
    (i k : Fin n) : tableSignature T m (finProdFinEquiv (i, k)) = T (i, m i) k := by
  simp only [tableSignature, Equiv.symm_apply_apply]

/-- The word of a selected signature concatenates the selected preimage words. -/
theorem ofFn_tableSignature {n : ℕ} (T : Table n) (m : Fin n → Bool) :
    List.ofFn (tableSignature T m) =
      (List.ofFn fun i : Fin n => List.ofFn (T (i, m i))).flatten := by
  have hblocks : FunFamily.blocks n n (tableSignature T m) = fun i => T (i, m i) := by
    funext i k
    rw [FunFamily.blocks_apply, tableSignature_apply]
  have h := FunFamily.ofFn_blocks_symm n n (FunFamily.blocks n n (tableSignature T m))
  rw [Equiv.symm_apply_apply, hblocks] at h
  exact h

/-- A message avoiding the planted cell has exactly its original signature. -/
theorem tableSignature_plant_of_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (m : Fin n → Bool) (hm : m i ≠ c) :
    tableSignature (plantTable T i c x) m = tableSignature T m := by
  funext j
  simp only [tableSignature]
  have hp : ((finProdFinEquiv.symm j).1, m (finProdFinEquiv.symm j).1) ≠ (i, c) := by
    intro h
    have hi := congrArg Prod.fst h
    have hc := congrArg Prod.snd h
    simp only at hi hc
    rw [hi] at hc
    exact hm hc
  rw [plantTable_ne T i c x hp]

/-- The public table applies the one-way map to every preimage. -/
def tablePublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (p : Fin n × Bool) : Y := g (T p)

/-- The public image at cell `p` is `g (T p)`. -/
theorem tablePublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (p : Fin n × Bool) : tablePublic g T p = g (T p) := rfl

/-- Replace the public image at `(i,c)` by `y`, without knowing a preimage of `y`. -/
def plantedPublic {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) : Y :=
  if p = (i, c) then y else g (T p)

/-- The planted public table reads `y` at `(i,c)` and the original images elsewhere. -/
theorem plantedPublic_eq {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y) (p : Fin n × Bool) :
    plantedPublic g T i c y p = if p = (i, c) then y else g (T p) := rfl

/-- When `y=g(x)`, the planted public table is the honest public table of the updated key. -/
theorem plantedPublic_image {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    plantedPublic g T i c (g x) = tablePublic g (plantTable T i c x) := by
  funext p
  by_cases hp : p = (i, c)
  · simp only [plantedPublic, tablePublic, plantTable, hp, if_true]
  · simp only [plantedPublic, tablePublic, plantTable, hp, if_false]

/-- The planted public table ignores the original preimage at its planted coordinate. -/
theorem plantedPublic_plant {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y) :
    plantedPublic g (plantTable T i c x) i c y = plantedPublic g T i c y := by
  funext p
  by_cases hp : p = (i, c)
  · rw [plantedPublic_eq, plantedPublic_eq, if_pos hp, if_pos hp]
  · rw [plantedPublic_eq, plantedPublic_eq, if_neg hp, if_neg hp,
      plantTable_ne T i c x hp]

/-- Extract the `i`-th preimage block from a flattened signature. -/
def signatureBlock {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) : Fin n → Bool :=
  fun k => σ (finProdFinEquiv (i, k))

/-- Extracted block `i` reads the flattened signature at indices `(i,k)`. -/
theorem signatureBlock_eq {n : ℕ} (σ : Fin (n * n) → Bool) (i : Fin n) :
    signatureBlock σ i = fun k => σ (finProdFinEquiv (i, k)) := rfl

/-- An accepting signature on a message with bit `c` at `i` supplies a preimage of `g(x)`
under the planted public table [PS10, Theorem 137.2]. -/
theorem extract_planted {n : ℕ} {Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (x : Fin n → Bool) (m : Fin n → Bool)
    (σ : Fin (n * n) → Bool)
    (hacc : ∀ j, g (signatureBlock σ j) = plantedPublic g T i c (g x) (j, m j))
    (hm : m i = c) : g (signatureBlock σ i) = g x := by
  have h := hacc i
  rw [plantedPublic_eq, hm, if_pos rfl] at h
  exact h

/-- A computation of cost zero under unit query costs is a return. -/
theorem exists_pure_of_cost_zero {ι α : Type} {spec : OracleSpec ι}
    (tree : OracleComp spec α) (h : tree.CostBoundedBy (fun _ => 1) 0) :
    ∃ a, tree = .pure a := by
  cases tree with
  | pure a => exact ⟨a, rfl⟩
  | query j m k =>
    have hcost := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 0).1 h
    omega

/-- The first query of a typed signature-forging computation, or `none` if it returns. -/
def firstQuery {n : ℕ} {α : Type} :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α → Option (Fin n → Bool)
  | .pure _ => none
  | .query _ m _ => some m

/-- A return has no first query. -/
theorem firstQuery_pure {n : ℕ} {α : Type} (a : α) :
    firstQuery (.pure a : OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = none := rfl

/-- A query node's first query is its own message. -/
theorem firstQuery_query {n : ℕ} {α : Type} (j : Fin 1) (m : Fin n → Bool)
    (k : (Fin (n * n) → Bool) → OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
    firstQuery (.query j m k) = some m := rfl

/-- The deterministic typed signing oracle returns the table's selected preimages. -/
def tableSigner {n : ℕ} (T : Table n) :
    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => .pure (tableSignature T m)

/-- The table signer is the stateless implementation of `m ↦ pure (tableSignature T m)`. -/
theorem tableSigner_eq {n : ℕ} (T : Table n) :
    tableSigner T = QueryImpl.ofComp (fun _ m => .pure (tableSignature T m)) := rfl

/-- The log of a computation with at most one query consists of its first query and answer,
or is empty if it returns immediately. -/
def firstLog {n : ℕ} {α : Type} (T : Table n) :
    OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α →
      QueryLog (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n))
  | .pure _ => []
  | .query j m _ => [⟨j, m, tableSignature T m⟩]

/-- A return has an empty first-query log. -/
theorem firstLog_pure {n : ℕ} {α : Type} (T : Table n) (a : α) :
    firstLog T (.pure a : OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) = [] := rfl

/-- A query node's first-query log contains exactly its message and deterministic answer. -/
theorem firstLog_query {n : ℕ} {α : Type} (T : Table n) (j : Fin 1) (m : Fin n → Bool)
    (k : (Fin (n * n) → Bool) → OracleComp
      (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α) :
    firstLog T (.query j m k) = [⟨j, m, tableSignature T m⟩] := rfl

/-- A computation with at most one query against the logged deterministic signer returns its
functional evaluation and exactly its first-query log.

**Proof sketch.** An immediate return has no log. At a query, the signer returns its selected
preimages and appends one entry. Unit query cost leaves cost zero for the continuation, so
the continuation is a return and appends no further entry. -/
theorem honest_transcript {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) :
    simulate (tableSigner T).withLog tree ((), []) =
      .pure (tree.evalFn (fun _ m => tableSignature T m), ((), firstLog T tree)) := by
  cases tree with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure, firstLog_pure]
  | query j m k =>
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (tableSignature T m))
      (by simpa only [Nat.sub_self] using hk.2 (tableSignature T m))
    simp only [simulate_query, QueryImpl.withLog_apply, tableSigner_eq, QueryImpl.ofComp_apply,
      OracleComp.pure_bind, ha, simulate_pure, OracleComp.evalFn_query,
      OracleComp.evalFn_pure, firstLog_query, List.nil_append]

/-- Freshness against the first-query log is exactly inequality with the optional first
message: no logged entry queried `m` if and only if `firstQuery tree ≠ some m`. -/
theorem fresh_firstLog_iff {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (m : Fin n → Bool) :
    (∀ e ∈ firstLog T tree, e.2.1 ≠ m) ↔ firstQuery tree ≠ some m := by
  cases tree <;> simp [firstLog, firstQuery]

/-- The logged one-query signing run has an output and log whose freshness condition is
equivalent to avoiding the optional first query, for any projection of a forgery's message. -/
theorem exists_honest_transcript {n : ℕ} {α : Type} (T : Table n)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (message : α → Fin n → Bool) :
    ∃ a log, simulate (tableSigner T).withLog tree ((), []) = .pure (a, ((), log)) ∧
      a = tree.evalFn (fun _ m => tableSignature T m) ∧
      ((∀ e ∈ log, e.2.1 ≠ message a) ↔ firstQuery tree ≠ some (message a)) := by
  exact ⟨_, _, honest_transcript T tree hcost, rfl, fresh_firstLog_iff T tree _⟩

/-- The sole signing query, if present, avoids the planted cell. -/
def Safe {n : ℕ} {α : Type}
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (i : Fin n) (c : Bool) : Prop :=
  ∀ m, firstQuery tree = some m → m i ≠ c

/-- Safety means that every message recorded as the first query has bit different from `c`. -/
theorem safe_iff {n : ℕ} {α : Type}
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (i : Fin n) (c : Bool) :
    Safe tree i c ↔ ∀ m, firstQuery tree = some m → m i ≠ c := Iff.rfl

/-- The aborting oracle answers an unsafe query with zero and answers a safe one honestly. -/
def abortingAnswer {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
    Fin (n * n) → Bool :=
  if m i = c then zeroBits _ else tableSignature T m

/-- An aborting answer is zero when `m i=c`, and otherwise is the original signature. -/
theorem abortingAnswer_eq {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) (m : Fin n → Bool) :
    abortingAnswer T i c m = if m i = c then zeroBits _ else tableSignature T m := rfl

/-- The aborting answer ignores the original preimage at the planted coordinate. -/
theorem abortingAnswer_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (m : Fin n → Bool) :
    abortingAnswer (plantTable T i c x) i c m = abortingAnswer T i c m := by
  rw [abortingAnswer_eq, abortingAnswer_eq]
  by_cases hm : m i = c
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, tableSignature_plant_of_safe T i c x m hm]

/-- The planted implementation remembers whether an unsafe query has occurred. -/
def abortingImpl {n : ℕ} (T : Table n) (i : Fin n) (c : Bool) :
    QueryImpl (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) Bool unifSpec :=
  fun _ m bad => .pure (abortingAnswer T i c m, bad || decide (m i = c))

/-- A call returns the aborting answer and sets its abort bit to `bad ∨ (m i=c)`. -/
theorem abortingImpl_apply {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (j : Fin 1) (m : Fin n → Bool) (bad : Bool) :
    abortingImpl T i c j m bad =
      .pure (abortingAnswer T i c m, bad || decide (m i = c)) := rfl

/-- The aborting implementation ignores the original preimage at its planted coordinate. -/
theorem abortingImpl_plant {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) :
    abortingImpl (plantTable T i c x) i c = abortingImpl T i c := by
  funext j m bad
  rw [abortingImpl_apply, abortingImpl_apply, abortingAnswer_plant]

/-- A safe call agrees with the updated key and leaves the abort bit false. -/
theorem abortingImpl_safe {n : ℕ} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool) (j : Fin 1) (m : Fin n → Bool) (hm : m i ≠ c) :
    abortingImpl T i c j m false = .pure (tableSignature (plantTable T i c x) m, false) := by
  rw [abortingImpl_apply, abortingAnswer_eq, if_neg hm,
    tableSignature_plant_of_safe T i c x m hm]
  simp only [hm, decide_false, Bool.false_or]

/-- A safe run with at most one signing query has exactly the honest output for the updated
key and never aborts [PS10, Theorem 137.2].

**Proof sketch.** A return needs no coupling. At a query, safety says that the queried message
does not reveal the planted cell, so its answer is exactly the updated key's honest answer.
The remaining computation has query cost zero and is a return; therefore the final outputs
agree and the abort flag stays false. -/
theorem planted_coupling {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c) :
    simulate (abortingImpl T i c) tree false =
      .pure (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m), false) := by
  cases tree with
  | pure a => rw [simulate_pure, OracleComp.evalFn_pure]
  | query j m k =>
    have hm : m i ≠ c := (safe_iff _ i c).1 hsafe m (firstQuery_query j m k)
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero
      (k (tableSignature (plantTable T i c x) m))
      (by simpa only [Nat.sub_self] using (hk.2 (tableSignature (plantTable T i c x) m)))
    rw [simulate_query, abortingImpl_safe T i c x j m hm, OracleComp.pure_bind, ha,
      simulate_pure, OracleComp.evalFn_query, ha, OracleComp.evalFn_pure]

/-- Run a fixed-position planted forger and extract block `i`, returning zero after an abort. -/
def extractionExperiment {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
  (simulate (abortingImpl T i c) tree false).bind fun res =>
    .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)

/-- The extraction experiment simulates the aborting implementation and selects the `i`-th
signature block when the final abort bit is false. -/
theorem extractionExperiment_eq {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    extractionExperiment T i c tree signature =
      (simulate (abortingImpl T i c) tree false).bind (fun res =>
        .pure (if res.2 then zeroBits n else signatureBlock (signature res.1) i)) := rfl

/-- The extraction experiment ignores the original preimage at the planted coordinate. -/
theorem extractionExperiment_plant {n : ℕ} {α : Type} (T : Table n) (i : Fin n)
    (c : Bool) (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    extractionExperiment (plantTable T i c x) i c tree signature =
      extractionExperiment T i c tree signature := by
  rw [extractionExperiment_eq, extractionExperiment_eq, abortingImpl_plant]

/-- The fixed-position reduction builds the planted public table, runs the forger against
the aborting signer, and extracts the `i`-th signature block. -/
def plantedExperiment {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) : ProbComp (Fin n → Bool) :=
  extractionExperiment T i c (adv (plantedPublic g T i c y)) signature

/-- The planted experiment is extraction after running the adversary on the planted public
table. -/
theorem plantedExperiment_eq {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y) (T : Table n)
    (i : Fin n) (c : Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    plantedExperiment g T i c y adv signature =
      extractionExperiment T i c (adv (plantedPublic g T i c y)) signature := rfl

/-- The entire planted experiment ignores the original preimage at `(i,c)`; this is the
coordinate-invariance hypothesis for sampling that preimage independently. -/
theorem plantedExperiment_plant {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool) (y : Y)
    (adv : ((Fin n × Bool) → Y) →
      OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) :
    plantedExperiment g (plantTable T i c x) i c y adv signature =
      plantedExperiment g T i c y adv signature := by
  rw [plantedExperiment_eq, plantedExperiment_eq, plantedPublic_plant,
    extractionExperiment_plant]

/-- A safe, accepting honest run whose forged message uses the planted bit produces an
inverse of the planted image in the reduction experiment [PS10, Theorem 137.2].

**Proof sketch.** The safe coupling identifies the reduction's output with the honest forged
signature block and keeps its abort bit false. Acceptance at the planted position then says
that applying the one-way map to that block gives the planted image. -/
theorem favorable_extraction {n : ℕ} {α Y : Type} (g : (Fin n → Bool) → Y)
    (T : Table n) (i : Fin n) (c : Bool) (x : Fin n → Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (signature : α → Fin (n * n) → Bool) (message : α → Fin n → Bool)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (hsafe : Safe tree i c)
    (hacc : ∀ j, g (signatureBlock
        (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) j) =
      plantedPublic g T i c (g x)
        (j, message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) j))
    (hm : message (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m)) i = c) :
    ∃ z, extractionExperiment T i c tree signature = .pure z ∧ g z = g x := by
  refine ⟨signatureBlock
    (signature (tree.evalFn (fun _ m => tableSignature (plantTable T i c x) m))) i, ?_, ?_⟩
  · rw [extractionExperiment_eq, planted_coupling T i c x tree hcost hsafe,
      OracleComp.pure_bind]
    rfl
  · exact extract_planted g T i c x _ _ hacc hm

end TCSlib.Cryptography.Authentication.LamportFill
