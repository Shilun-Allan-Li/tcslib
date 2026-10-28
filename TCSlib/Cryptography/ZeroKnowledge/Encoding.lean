/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.Permutations
import TCSlib.Cryptography.ZeroKnowledge.EncodingPermutations
import TCSlib.Complexity.ClassNP.PolyTimePairing
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Sqrt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String encodings for the graph protocols

The string layer of Chapter 4 (Inf-4.1, Inf-4.2): the typed objects of the graph protocols
[PS10, §4.5–§4.7] — graphs on `Fin n` as adjacency matrices, permutations of `Fin n`,
`3`-colourings — with their encodings as bit strings, total decoders with defaults, the
decode-encode identities, the coin table that reads the random tape of a party as the
`n × T × k` array consumed by the rejection-sampled permutation `permFromCoins` of
`Asymptotic/Permutations.lean` (D10), and the polynomial-time computability statements of the
honest parties' string operations (Inf-4.2: applying a permutation to a graph, composing
permutations, sampling a permutation from coins).

Graphs are arbitrary Boolean relations `Fin n → Fin n → Bool` (loops and asymmetry allowed):
the protocols never use simplicity, and the encoding is the row-major `n²`-bit matrix with
`n` recovered as `Nat.sqrt` of the length. `permGraph G π u v := G (π⁻¹ u) (π⁻¹ v)` is the
relabelled graph `π(G)` of [PS10, §4.5] (`π(G)` has edge `(π u, π v)` iff `G` has `(u, v)`).

**Deviation (D10, Inf-4.2):** a uniformly random permutation `σ ← S_n` of [PS10, Protocols
118.3, 120.6, 127.5] is sampled from a bit-coin tape by `permFromCoins` (rejection sampling
with `T` trials of `k` bits per position), which fails with probability at most
`n (1 - 2^{-k})^T`; at the campaign parameters `permBits n = Nat.size n`,
`permTrials n = 2n²` the failure probability is at most `n · 2^{-n}`
(`uprob_permFromCoins_none_le_two_pow`), and the protocol theorems carry this statistical
term.

## Main definitions

* `TCSlib.Cryptography.Graph`, `TCSlib.Cryptography.permGraph` — graphs on `Fin n` and the
  relabelling `π(G)` [PS10, §4.5] (Def-117.e, string side).
* `TCSlib.Cryptography.encGraph`, `TCSlib.Cryptography.decGraph` — adjacency-matrix encoding
  and total decoding.
* `TCSlib.Cryptography.encPerm`, `TCSlib.Cryptography.decPerm` — the relation-matrix encoding
  of a permutation and its total decoding (identity on malformed words).
* `TCSlib.Cryptography.encColoring`, `TCSlib.Cryptography.decColoring` — two bits per vertex
  for `Fin 3`-colourings [PS10, Protocol 127.5].
* `TCSlib.Cryptography.coinTable` — the `n × T × k` coin array read from a random tape.

## Main results

* `TCSlib.Cryptography.permGraph_one`, `TCSlib.Cryptography.permGraph_mul` — relabelling is
  a right action: `1(G) = G`, `σ(π(G)) = (σ π)(G)` (the algebra of [PS10, Lemma 120.a]).
* `TCSlib.Cryptography.decGraph_encGraph`, `TCSlib.Cryptography.decPerm_encPerm`,
  `TCSlib.Cryptography.decColoring_encColoring` — decode-encode identities (proved);
  `TCSlib.Cryptography.encGraph_injective`, `TCSlib.Cryptography.encPerm_injective`.
* `TCSlib.Cryptography.pushesUniform_coinTable` — a uniform tape of `n T k` bits gives a
  uniform coin table (`coinTable_ofFn`).
* `TCSlib.Cryptography.encGraph_getD_nat`, `TCSlib.Cryptography.encPerm_getD_nat`,
  `TCSlib.Cryptography.decPerm_val`, `TCSlib.Cryptography.decPerm_symm_val` — numeric access
  to the encodings and the identification of `decPerm` with the numeric decoder model of
  `EncodingPermutations.lean` (`EncodingMachines.permNum`, `permInvNum`).
* `TCSlib.Cryptography.polyTimeComputable_encPermGraph`,
  `TCSlib.Cryptography.polyTimeComputable_encPermMulInv`,
  `TCSlib.Cryptography.polyTimeComputable_encPermFromCoins` — the honest parties' string
  operations are polynomial-time (Inf-4.2), through the bit-extraction principle and the
  numeric models of `EncodingMachines.lean` and `EncodingPermutations.lean`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6; §4.7 Protocol 127.5.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 1, string encodings of combinatorial objects.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Graphs and relabelling -/

/-- A graph on the vertex set `Fin n` as a Boolean adjacency relation [PS10, §4.5]
(Def-117.e, string side; simplicity is not needed by the protocols). -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- The relabelled graph `π(G)` [PS10, §4.5]: `π(G)` has the edge `(π u, π v)` exactly when
`G` has the edge `(u, v)`, i.e. `π(G) u v = G (π⁻¹ u) (π⁻¹ v)`. -/
def permGraph {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) : Graph n :=
  fun u v => G (π.symm u) (π.symm v)

/-- Unfolding of `permGraph`. -/
@[simp] theorem permGraph_apply {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    permGraph G π u v = G (π.symm u) (π.symm v) := rfl

/-- The identity relabelling is the identity. -/
@[simp] theorem permGraph_one {n : ℕ} (G : Graph n) : permGraph G 1 = G := rfl

/-- Relabelling is a right action: `σ(π(G)) = (σ * π)(G)` (the algebra behind
[PS10, Proposition 120.7], completeness: `(π σ⁻¹)(σ(G₀)) = π(G₀)`). -/
theorem permGraph_mul {n : ℕ} (G : Graph n) (π σ : Equiv.Perm (Fin n)) :
    permGraph (permGraph G π) σ = permGraph G (σ * π) := by
  funext u v
  simp [permGraph, Equiv.Perm.mul_def]

/-- Relabelling by `π` and then by `π⁻¹` gives the graph back. -/
theorem permGraph_permGraph_inv {n : ℕ} (G : Graph n) (π : Equiv.Perm (Fin n)) :
    permGraph (permGraph G π) π⁻¹ = G := by
  rw [permGraph_mul, inv_mul_cancel, permGraph_one]

/-- The completeness identity of the graph-isomorphism protocol [PS10, Proposition 120.7]
(Lem-120.a): if `σ(G₀) = G₁` and `H = π(G₀)` then `(π σ⁻¹)(G₁) = H`. -/
theorem permGraph_mul_inv_of_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) :
    permGraph G₁ (π * σ⁻¹) = permGraph G₀ π := by
  rw [← hσ, permGraph_mul, inv_mul_cancel_right]

/-! ### Encodings of graphs -/

/-- The adjacency-matrix encoding of a graph: `n²` bits in row-major order (entry `(u, v)` at
position `finProdFinEquiv (u, v) = u * n + v`). -/
def encGraph {n : ℕ} (G : Graph n) : List Bool :=
  List.ofFn fun k : Fin (n * n) => G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The total decoding of a graph: the number of vertices is `Nat.sqrt` of the length, the
entries are read with default `false`. -/
def decGraph (w : List Bool) : Σ n, Graph n :=
  ⟨Nat.sqrt w.length, fun u v => w.getD (finProdFinEquiv (u, v)) false⟩

/-- An encoded graph on `n` vertices has `n²` bits. -/
@[simp] theorem length_encGraph {n : ℕ} (G : Graph n) : (encGraph G).length = n * n := by
  simp [encGraph]

/-- The entries of an encoded graph. -/
theorem encGraph_getD {n : ℕ} (G : Graph n) (u v : Fin n) :
    (encGraph G).getD (finProdFinEquiv (u, v)) false = G u v := by
  have hk : (finProdFinEquiv (u, v) : ℕ) < (encGraph G).length := by
    rw [length_encGraph]
    exact (finProdFinEquiv (u, v)).isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [encGraph, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]

/-- Decoding an encoded graph gives the graph back (Inf-4.1). -/
theorem decGraph_encGraph {n : ℕ} (G : Graph n) : decGraph (encGraph G) = ⟨n, G⟩ := by
  have hn : Nat.sqrt (encGraph G).length = n := by rw [length_encGraph, Nat.sqrt_eq]
  unfold decGraph
  rw [hn, Sigma.mk.inj_iff]
  exact ⟨rfl, heq_of_eq (funext fun u => funext fun v => encGraph_getD G u v)⟩

/-- The encoding of graphs is injective. -/
theorem encGraph_injective (n : ℕ) : Function.Injective (encGraph (n := n)) := by
  intro G G' h
  funext u v
  rw [← encGraph_getD G, ← encGraph_getD G', h]

/-! ### Encodings of permutations -/

/-- The relation-matrix encoding of a permutation: bit `(i, j)` is `decide (π i = j)`. -/
def encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : List Bool :=
  List.ofFn fun k : Fin (n * n) =>
    decide (π (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k).2)

/-- The total decoding of a permutation of `Fin n`: row `i` is read as the least `j` with bit
`(i, j)` set (default `i`); if the resulting map is bijective it is the permutation, otherwise
the identity. -/
noncomputable def decPerm (n : ℕ) (w : List Bool) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Function.Bijective (fun i : Fin n =>
      (Fin.find (fun j : Fin n => w.getD (finProdFinEquiv (i, j)) false = true)).getD i)
    then Equiv.ofBijective _ h else 1

/-- An encoded permutation of `Fin n` has `n²` bits. -/
@[simp] theorem length_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : (encPerm π).length = n * n := by
  simp [encPerm]

/-- The entries of an encoded permutation. -/
theorem encPerm_getD {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (encPerm π).getD (finProdFinEquiv (i, j)) false = decide (π i = j) := by
  have hk : (finProdFinEquiv (i, j) : ℕ) < (encPerm π).length := by
    rw [length_encPerm]
    exact (finProdFinEquiv (i, j)).isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  simp only [encPerm, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]

/-- Row `i` of an encoded permutation has exactly one set bit, at column `π i`: the decoder's
search finds it (for any decidability instance of the search predicate). -/
theorem encPerm_find_row {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n)
    [DecidablePred fun j : Fin n => (encPerm π).getD (finProdFinEquiv (i, j)) false = true] :
    Fin.find (fun j : Fin n => (encPerm π).getD (finProdFinEquiv (i, j)) false = true) =
      some (π i) := by
  rw [← Option.mem_def, Fin.mem_find_iff]
  refine ⟨by rw [encPerm_getD]; simp, fun j hj => ?_⟩
  rw [encPerm_getD] at hj
  exact le_of_eq (by simpa using hj)

/-- Decoding an encoded permutation gives the permutation back (Inf-4.1): by
`encPerm_find_row` the decoded map is `⇑π`, which is bijective, so the decoder's first branch
applies and `Equiv.ofBijective ⇑π _ = π`. -/
theorem decPerm_encPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : decPerm n (encPerm π) = π := by
  unfold decPerm
  split_ifs with h
  · refine Equiv.ext fun i => ?_
    rw [Equiv.ofBijective_apply]
    show (Fin.find _).getD i = π i
    rw [encPerm_find_row, Option.getD_some]
  · exfalso
    apply h
    convert π.bijective using 1
    funext i
    rw [encPerm_find_row, Option.getD_some]

/-- The encoding of permutations is injective. -/
theorem encPerm_injective (n : ℕ) : Function.Injective (encPerm (n := n)) := by
  intro π π' h
  refine Equiv.ext fun i => ?_
  have h1 := encPerm_getD π i (π i)
  rw [h, encPerm_getD] at h1
  have h2 : π' i = π i := by simpa using h1.symm
  exact h2.symm

/-! ### Encodings of colourings -/

/-- The encoding of a `3`-colouring of `Fin n` [PS10, Protocol 127.5]: two bits per vertex
(the colour `c ∈ {0, 1, 2}` as `[c / 2 = 1, c % 2 = 1]`), `2n` bits in all. -/
def encColoring {n : ℕ} (c : Fin n → Fin 3) : List Bool :=
  List.ofFn fun k : Fin (n * 2) =>
    let i := (finProdFinEquiv.symm k).1
    let b := (finProdFinEquiv.symm k).2
    if b = 0 then decide ((c i).val / 2 = 1) else decide ((c i).val % 2 = 1)

/-- The total decoding of a `3`-colouring of `Fin n`: the two bits of vertex `i` are read with
default `false` and combined modulo `3`. -/
def decColoring (n : ℕ) (w : List Bool) : Fin n → Fin 3 := fun i =>
  ⟨(2 * (w.getD (finProdFinEquiv (i, (0 : Fin 2))) false).toNat +
      (w.getD (finProdFinEquiv (i, (1 : Fin 2))) false).toNat) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- An encoded colouring of `n` vertices has `2n` bits. -/
@[simp] theorem length_encColoring {n : ℕ} (c : Fin n → Fin 3) :
    (encColoring c).length = n * 2 := by
  simp [encColoring]

/-- Decoding an encoded colouring gives the colouring back (Inf-4.1): the two bits of vertex
`i` are `decide (c i / 2 = 1)` and `decide (c i % 2 = 1)`, and for `c i ∈ {0, 1, 2}` the
number `2 · [c i / 2 = 1] + [c i % 2 = 1]` is `c i` (checked by `decide`). -/
theorem decColoring_encColoring {n : ℕ} (c : Fin n → Fin 3) : decColoring n (encColoring c) = c := by
  funext i
  have hget : ∀ b : Fin 2, (encColoring c).getD (finProdFinEquiv (i, b)) false =
      if b = 0 then decide ((c i).val / 2 = 1) else decide ((c i).val % 2 = 1) := by
    intro b
    have hk : (finProdFinEquiv (i, b) : ℕ) < (encColoring c).length := by
      rw [length_encColoring]
      exact (finProdFinEquiv (i, b)).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    simp only [encColoring, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hval : ∀ x : Fin 3,
      (2 * (decide (x.val / 2 = 1)).toNat + (decide (x.val % 2 = 1)).toNat) % 3 = x.val := by
    decide
  apply Fin.ext
  simp only [decColoring, hget, if_true, Fin.isValue, one_ne_zero, if_false]
  exact hval (c i)

/-! ### Coin tables -/

/-- The `n × T × k` coin array read from a random tape (bit `(i, t, j)` at position
`(i T + t) k + j`, default `false`): the input of `permFromCoins n k T` for a party whose
random tape is a string (D10). -/
def coinTable (n T k : ℕ) (r : List Bool) : Fin n → Fin T → Fin k → Bool :=
  fun i t j => r.getD (((i * T) + t) * k + j) false

/-- Unfolding of `coinTable`. -/
@[simp] theorem coinTable_apply (n T k : ℕ) (r : List Bool) (i : Fin n) (t : Fin T) (j : Fin k) :
    coinTable n T k r i t j = r.getD (((i * T) + t) * k + j) false := rfl

/-- The entries of the coin table of a tape of exactly `n T k` bits: entry `(i, t, j)` is the
tape bit at the index `finProdFinEquiv (finProdFinEquiv (i, t), j) = (i T + t) k + j`. -/
theorem coinTable_ofFn (n T k : ℕ) (r : Fin (n * T * k) → Bool) (i : Fin n) (t : Fin T)
    (j : Fin k) :
    coinTable n T k (List.ofFn r) i t j = r (finProdFinEquiv (finProdFinEquiv (i, t), j)) := by
  have hm : ((finProdFinEquiv (finProdFinEquiv (i, t), j) : Fin (n * T * k)) : ℕ) =
      ((i * T) + t) * k + j := by
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [coinTable_apply, ← hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _),
    Option.getD_some, Fin.eta]

/-- A uniform tape of `n T k` bits gives a uniform coin table: the map from tapes of length
`n T k` to tables is a bijection, hence pushes the uniform distribution to the uniform one
(the step that lets the ideal `permFromCoins` lemmas of `Sampling.lean` be applied to a party
sampling its permutation from its random tape).

**Proof sketch.** The index map `(i, t, j) ↦ (i T + t) k + j` is the bijection
`Fin n × Fin T × Fin k ≃ Fin (n T k)` (`finProdFinEquiv` twice, `Nat.lt_of_lt_of_le` for the
range), so `r ↦ coinTable n T k (List.ofFn r)` is the curried reindexing
`(Fin (n T k) → Bool) ≃ (Fin n → Fin T → Fin k → Bool)` (`Equiv.piCongrLeft`, `Equiv.curry`),
and `HardcoreBit.pushesUniform_equiv` applies (`List.getD_eq_getElem?_getD`,
`List.getElem?_ofFn` identify the entries). -/
theorem pushesUniform_coinTable (n T k : ℕ) :
    HardcoreBit.PushesUniform
      (fun r : Fin (n * T * k) → Bool => coinTable n T k (List.ofFn r)) := by
  have hbij : Function.Bijective
      (fun r : Fin (n * T * k) → Bool => coinTable n T k (List.ofFn r)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun r r' h => ?_, ?_⟩
    · funext m
      have h1 := congrFun (congrFun (congrFun h
        (finProdFinEquiv.symm (finProdFinEquiv.symm m).1).1)
        (finProdFinEquiv.symm (finProdFinEquiv.symm m).1).2) (finProdFinEquiv.symm m).2
      dsimp only at h1
      rwa [coinTable_ofFn, coinTable_ofFn, Prod.mk.eta, Equiv.apply_symm_apply, Prod.mk.eta,
        Equiv.apply_symm_apply] at h1
    · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul]
      ring_nf
  exact HardcoreBit.pushesUniform_equiv (Equiv.ofBijective _ hbij)

/-! ### Numeric access to the encodings -/

/-- Bit `v + n u` of an encoded graph is the entry `(u, v)` (`encGraph_getD` with
`finProdFinEquiv_apply_val`). -/
theorem encGraph_getD_nat {n : ℕ} (G : Graph n) (u v : Fin n) :
    (encGraph G).getD (v + n * u) false = G u v := by
  have h := encGraph_getD G u v
  rwa [finProdFinEquiv_apply_val] at h

/-- Bits beyond `n²` of an encoded graph read `false`. -/
theorem encGraph_getD_of_le {n : ℕ} (G : Graph n) {m : ℕ} (hm : n * n ≤ m) :
    (encGraph G).getD m false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_encGraph]; exact hm)]
  rfl

/-- Bit `j + n i` of an encoded permutation is `decide (π i = j)`. -/
theorem encPerm_getD_nat {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (encPerm π).getD (j + n * i) false = decide (π i = j) := by
  have h := encPerm_getD π i j
  rwa [finProdFinEquiv_apply_val] at h

/-- Bits beyond `n²` of an encoded permutation read `false`. -/
theorem encPerm_getD_of_le {n : ℕ} (π : Equiv.Perm (Fin n)) {m : ℕ} (hm : n * n ≤ m) :
    (encPerm π).getD m false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_encPerm]; exact hm)]
  rfl

/-- The row-major index of `(i, j)` in the two conventions: `i n + j = j + n i`. -/
theorem idx_comm (n i j : ℕ) : i * n + j = j + n * i := by ring

/-! ### The numeric model of the decoder -/

open EncodingMachines in
/-- The decoded map of `decPerm` (row `i` ↦ its first set column, default `i`) is `rowMap`
numerically.

**Proof sketch.** Case on `Fin.find`. If it is `none` (`Fin.find_eq_none_iff`) no column of row
`i` is set, so the search `rowFirst` is exhausted (`firstIdx_eq_of_forall`) and both sides are
`i`. If it is `some j` (`Fin.find_eq_some_iff`: `j` is set and minimal) the search returns `j`
(`firstIdx_eq_of`), which is below `n`, so `rowMap` is `j` too. The two index conventions
`finProdFinEquiv (i, j) = j + n i` and `i n + j` agree by `idx_comm`. -/
theorem decPerm_map_val {n : ℕ} (b : List Bool) (i : Fin n)
    [DecidablePred fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true] :
    (((Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i : Fin n) :
      ℕ) = rowMap n b i := by
  unfold rowMap rowFirst
  cases h : Fin.find (fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true) with
  | none =>
    rw [Fin.find_eq_none_iff] at h
    rw [Option.getD_none, if_pos]
    apply firstIdx_eq_of_forall
    intro j hj
    have := h ⟨j, hj⟩
    rw [finProdFinEquiv_apply_val] at this
    rw [idx_comm]
    exact Bool.eq_false_iff.2 this
  | some j =>
    rw [Fin.find_eq_some_iff] at h
    obtain ⟨hj, hmin⟩ := h
    rw [Option.getD_some]
    have hfirst : firstIdx (fun j' => b.getD (↑i * n + j') false) n = j := by
      apply firstIdx_eq_of j.isLt
      · rw [finProdFinEquiv_apply_val] at hj
        rw [idx_comm]
        exact hj
      · intro j' hj'
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hle := hmin ⟨j', lt_trans hj' j.isLt⟩
          (by rw [finProdFinEquiv_apply_val]; rw [idx_comm] at hc; exact hc)
        exact absurd hle (not_le.2 hj')
    rw [hfirst, if_neg j.isLt.ne]

open EncodingMachines in
/-- The decoded map of `decPerm` is bijective iff the numeric surjectivity test `isBij` holds
(`Finite.surjective_iff_bijective`, `isBij_iff`, `decPerm_map_val`). -/
theorem decPerm_bijective_iff {n : ℕ} (b : List Bool)
    [∀ i : Fin n, DecidablePred fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true] :
    Function.Bijective (fun i : Fin n =>
        (Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i) ↔
      isBij n b = true := by
  rw [isBij_iff, ← Finite.surjective_iff_bijective]
  constructor
  · intro hs u hu
    obtain ⟨i, hi⟩ := hs ⟨u, hu⟩
    simp only at hi
    exact ⟨i, i.isLt, by rw [← decPerm_map_val, hi]⟩
  · intro h u
    obtain ⟨i, hi, hiu⟩ := h u u.isLt
    exact ⟨⟨i, hi⟩, Fin.ext (by rw [decPerm_map_val]; exact hiu)⟩

open EncodingMachines in
/-- The decoded permutation, numerically: `decPerm n b i = permNum n b i`. -/
theorem decPerm_val {n : ℕ} (b : List Bool) (i : Fin n) :
    ((decPerm n b i : Fin n) : ℕ) = permNum n b i := by
  classical
  unfold decPerm permNum
  split_ifs with h1 h2 h2
  · rw [Equiv.ofBijective_apply]
    exact decPerm_map_val b i
  · exact absurd ((decPerm_bijective_iff b).1 h1) h2
  · exact absurd ((decPerm_bijective_iff b).2 h2) h1
  · rfl

open EncodingMachines in
/-- The inverse of the decoded permutation, numerically: `(decPerm n b)⁻¹ u = permInvNum n b u`.

**Proof sketch.** Unfold `decPerm`; the two branches agree with those of `permInvNum` by
`decPerm_bijective_iff`. In the bijective branch `i := (ofBijective map _).symm u` satisfies
`map i = u` (`Equiv.ofBijective_apply_symm_apply`), i.e. `rowMap n b i = u`
(`decPerm_map_val`), and no `i' < i` does (injectivity), so the search `rowInv` returns `i`
(`firstIdx_eq_of`). In the other branch both sides are the identity. -/
theorem decPerm_symm_val {n : ℕ} (b : List Bool) (u : Fin n) :
    (((decPerm n b).symm u : Fin n) : ℕ) = permInvNum n b u := by
  classical
  unfold decPerm permInvNum
  split_ifs with h1 h2 h2
  · have hmap := Equiv.ofBijective_apply_symm_apply _ h1 u
    unfold rowInv
    symm
    apply firstIdx_eq_of (Fin.isLt _)
    · rw [decide_eq_true_eq, ← decPerm_map_val, hmap]
    · intro i' hi'
      rw [decide_eq_false_iff_not]
      intro heq
      have hpre : (fun i : Fin n =>
          (Fin.find fun j : Fin n => b.getD (finProdFinEquiv (i, j)) false = true).getD i)
            ⟨i', lt_trans hi' (Fin.isLt _)⟩ = u :=
        Fin.ext (by rw [decPerm_map_val]; exact heq)
      have hval : (((Equiv.ofBijective _ h1).symm u : Fin n) : ℕ) = i' :=
        (congrArg Fin.val (h1.1 (hpre.trans hmap.symm))).symm
      omega
  · exact absurd ((decPerm_bijective_iff b).1 h1) h2
  · exact absurd ((decPerm_bijective_iff b).2 h2) h1
  · rfl

/-- `2^{Nat.size n} ≤ 2 n + 1` (`two_pow_permBits_le` for `n ≥ 1`, `1 ≤ 1` for `n = 0`): the
bound threaded through the block-value loops of the permutation sampler. -/
theorem two_pow_size_le_two_mul_succ (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_pow_permBits_le hn).trans (Nat.le_succ _)

/-! ### Polynomial-time string operations of the honest parties (Inf-4.2) -/

/-- Applying an encoded permutation to an encoded graph is polynomial-time
(`⟨encGraph G, encPerm π⟩ ↦ encGraph (π(G))`; the honest prover's first message in
[PS10, Protocol 120.6] and the relabelled graph of [PS10, Protocol 118.3]) (Inf-4.2).

**Proof sketch.** Both inputs have `n²` bits with `n = Nat.sqrt |·|`; the output bit at
position `(u, v)` is the input bit of `G` at `(π⁻¹ u, π⁻¹ v)`, where `π⁻¹ u` is the row index
`i` whose bit `(i, u)` is set. Machine: `polyTimeComputable_blockMap` over the `n²` output
positions (block length `1`, with the whole input threaded as the first pair component), each
block computed by a scan of the two matrices (`polyTimeComputable_iterateFind` over the `n`
candidate rows, the test being `polyTimeComputable_pairEq` on the relevant bits extracted by
`pairTakePoly`/`pairDropPoly`); `Nat.sqrt` is computed by iterating `polyTimeComputable_lenLe`
against `unaryPoly` squares (`polyTimeComputable_iterateFind`, at most `|w|` rounds). All
budgets are polynomial in the input length. -/
theorem polyTimeComputable_encPermGraph :
    PolyTimeComputable fun z =>
      encGraph (permGraph (decGraph (pairFstD z)).2 (decPerm _ (pairSndD z))) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encGraph (permGraph (decGraph (pairFstD z)).2 (decPerm _ (pairSndD z)))).length true := by
    simpa only [length_encGraph] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have ha : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hu := permInvNum_poly hN' hb (divNum_poly hm hN')
  have hv := permInvNum_poly hN' hb (modNum_poly hm hN')
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (getBit_poly ha (unaryAdd_poly hv (unaryMul_poly hN' hu))) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  show [(encGraph (permGraph (n := n) (decGraph (pairFstD (pairSndD w))).2
    (decPerm n (pairSndD (pairSndD w))))).getD m false] = _
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    conv_lhs => rw [hidx]
    rw [encGraph_getD_nat, permGraph_apply]
    show [(pairFstD (pairSndD w)).getD (finProdFinEquiv _) false] = _
    rw [finProdFinEquiv_apply_val, decPerm_symm_val, decPerm_symm_val]
  · rw [encGraph_getD_of_le _ (not_lt.1 hlt)]

/-- Composing an encoded permutation with the inverse of another is polynomial-time
(`⟨encPerm π, encPerm σ⟩ ↦ encPerm (π σ⁻¹)` at `n = Nat.sqrt |encPerm π|`; the honest prover's
third message in [PS10, Protocol 120.6]) (Inf-4.2).

**Proof sketch.** Output bit `(i, j)` is set iff `π (σ⁻¹ i) = j`, i.e. iff the row `l` with
bit `(l, i)` of `σ` set has bit `(l, j)` of `π` set: for each of the `n²` output positions
(`polyTimeComputable_blockMap`) a scan over the `n` rows (`polyTimeComputable_iterateFind`)
with bit tests by `pairTakePoly`/`pairDropPoly` and `polyTimeComputable_pairEq`; the decoder's
bijectivity test and the identity fallback are `polyTimeComputable_ite` over a scan checking
that every row and every column has exactly one set bit. -/
theorem polyTimeComputable_encPermMulInv :
    PolyTimeComputable fun z =>
      encPerm (decPerm (Nat.sqrt (pairFstD z).length) (pairFstD z) *
        (decPerm (Nat.sqrt (pairFstD z).length) (pairSndD z))⁻¹) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encPerm (decPerm (Nat.sqrt (pairFstD z).length) (pairFstD z) *
        (decPerm (Nat.sqrt (pairFstD z).length) (pairSndD z))⁻¹)).length true := by
    simpa only [length_encPerm] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have ha : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hi := permNum_poly hN' ha (permInvNum_poly hN' hb (divNum_poly hm hN'))
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (eqTest_poly hi (modNum_poly hm hN')) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    conv_lhs => rw [hidx]
    rw [encPerm_getD_nat, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    congr 1
    rw [decide_eq_decide, Fin.ext_iff, decPerm_val, decPerm_symm_val]
  · rw [encPerm_getD_of_le _ (not_lt.1 hlt)]

/-- Sampling a permutation of the vertices of an encoded graph from a random tape is
polynomial-time: `⟨encGraph G, r⟩ ↦ encPerm (permFromCoins n (permBits n) (permTrials n)
(coinTable n (permTrials n) (permBits n) r))` with `n = (decGraph (encGraph G)).1` and the
identity on failure — the honest parties' `σ ← S_n` of [PS10, Protocols 118.3, 120.6 and
127.5] under D10 at the campaign parameters (Inf-4.2); it is the shared string form of
`samplePerm` (`ZeroKnowledge/GraphIsomorphism.lean`).

**Repair (run-3 audit P2-1):** restated at the campaign parameters `permBits n = Nat.size n`
bits per trial and `permTrials n = 2n²` trials per position (`Asymptotic/Permutations.lean`);
the frozen `permFromCoins n n n` fails almost surely. The private
`polyTimeComputable_encSamplePerm` of `GraphIsomorphism.lean` is derived from this lemma.
(Run-3 audit P9-2, which reported the run-2 statement at `permFromCoins n n n` as diverging
from `samplePerm`, is resolved by the same repair: `samplePerm n r` unfolds to the sampler
stated here, so the lemma is the one the fill phase proves.)

**Proof sketch.** `n = Nat.sqrt |encGraph G|` (as in `polyTimeComputable_encPermGraph`), and
`1^{permBits n}` by `polyTimeComputable_lenLe` against the `unaryPoly` powers of two
(`polyTimeComputable_iterateFind`, at most `n` rounds). For each position `i < n`
(`polyTimeComputable_iterateEmit` over `i`), the `2n²` trials of `permBits n` bits are the
blocks of the tape (`polyTimeComputable_blockMap` with the unary block length), each read as a
number and compared with `n - i` (`bitsToNat` in binary by `computesFunInTime_polyBits`-style
arithmetic, or in unary by `unaryPoly` and `polyTimeComputable_lenLe`), the first accepted
one being `polyTimeComputable_iterateFind`; the Fisher–Yates product of the `n` transpositions
is accumulated as an `n²`-bit relation matrix (`polyTimeComputable_iterate` over `n` rounds,
each round swapping two rows); failure of any position selects the identity matrix
(`polyTimeComputable_ite`). -/
theorem polyTimeComputable_encPermFromCoins :
    PolyTimeComputable fun z =>
      encPerm ((permFromCoins (decGraph (pairFstD z)).1 (permBits (decGraph (pairFstD z)).1)
        (permTrials (decGraph (pairFstD z)).1)
        (coinTable (decGraph (pairFstD z)).1 (permTrials (decGraph (pairFstD z)).1)
          (permBits (decGraph (pairFstD z)).1) (pairSndD z))).getD 1) := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun z => List.replicate (Nat.sqrt (pairFstD z).length) true :=
    unarySqrt_poly (unaryLength_poly polyTimeComputable_pairFstD)
  have hlen : PolyTimeComputable fun z => List.replicate
      (encPerm ((permFromCoins (decGraph (pairFstD z)).1 (permBits (decGraph (pairFstD z)).1)
        (permTrials (decGraph (pairFstD z)).1)
        (coinTable (decGraph (pairFstD z)).1 (permTrials (decGraph (pairFstD z)).1)
          (permBits (decGraph (pairFstD z)).1) (pairSndD z))).getD 1)).length true := by
    simpa only [length_encPerm] using unaryMul_poly hN hN
  refine polyTimeComputable_of_getD ?_ hlen
  have hN' : PolyTimeComputable fun w =>
      List.replicate (Nat.sqrt (pairFstD (pairSndD w)).length) true :=
    unaryComp_poly hN polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hr : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hK := unarySize_poly hN'
  have hT := unaryMul_poly (unaryMul_poly (unaryConst_poly 2) hN') hN'
  have hM := unaryAdd_poly (unaryMul_poly (unaryConst_poly 2) hN') (unaryConst_poly 1)
  have hX := unaryMin_poly (divNum_poly hm hN') hN'
  have hval := permFromCoinsNum_poly hN' hK hT hr hX hM
    (fun w => two_pow_size_le_two_mul_succ _) (fun w => min_le_right _ _)
  have hbit := polyTimeComputable_ite (ltTest_poly hm (unaryMul_poly hN' hN'))
    (eqTest_poly hval (modNum_poly hm hN')) (polyTimeComputable_const [false])
  convert hbit using 1
  funext w
  simp only [decide_eq_true_eq, divNum_eq, modNum_eq]
  show [(encPerm ((permFromCoins (Nat.sqrt (pairFstD (pairSndD w)).length)
      (permBits (Nat.sqrt (pairFstD (pairSndD w)).length))
      (permTrials (Nat.sqrt (pairFstD (pairSndD w)).length))
      (coinTable (Nat.sqrt (pairFstD (pairSndD w)).length)
        (permTrials (Nat.sqrt (pairFstD (pairSndD w)).length))
        (permBits (Nat.sqrt (pairFstD (pairSndD w)).length)) (pairSndD (pairSndD w)))).getD 1)).getD
    (pairFstD w).length false] = _
  set n := Nat.sqrt (pairFstD (pairSndD w)).length with hn
  set m := (pairFstD w).length with hm_def
  split_ifs with hlt
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h] at hlt; simp at hlt)
    have hu' : m / n < n := (Nat.div_lt_iff_lt_mul hn0).2 hlt
    have hv' : m % n < n := Nat.mod_lt _ hn0
    have hidx : m = (⟨m % n, hv'⟩ : Fin n) + n * (⟨m / n, hu'⟩ : Fin n) :=
      (Nat.mod_add_div m n).symm
    rw [min_eq_left hu'.le]
    conv_lhs => rw [hidx]
    rw [encPerm_getD_nat]
    congr 1
    rw [decide_eq_decide, Fin.ext_iff,
      permFromCoins_getD_val (r := pairSndD (pairSndD w))
        (b := coinTable n (permTrials n) (permBits n) (pairSndD (pairSndD w))) (fun _ _ _ => rfl)]
    rfl
  · rw [encPerm_getD_of_le _ (not_lt.1 hlt)]

end TCSlib.Cryptography
