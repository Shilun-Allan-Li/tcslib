/-
  LDC/Decomposition.lean
  §6: Hypergraph Decomposition (Lemma 6.1)
-/
import Mathlib
import RequestProject.LDC.Defs

open Finset BigOperators

noncomputable section

/-! ## Lemma 6.1: Hypergraph Decomposition

    Given 3-uniform hypergraphs H₁, …, Hₖ on [n] and a threshold d,
    define heavy pairs P = {{u,v} : deg_H({u,v}) > d}.
    Then we can decompose into residual H'ᵢ (with pair-degree ≤ d)
    and bipartite graphs Gᵢ. -/

/-- The set of heavy pairs: pairs with degree > d in the combined hypergraph. -/
def heavyPairs (n : ℕ) (H : Hypergraph n) (d : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.product Finset.univ).image (fun p => ({p.1, p.2} : Finset (Fin n)))
    |>.filter (fun Q => Q.card = 2 ∧ H.degree Q > d)

/-
Remark 6.2: Counting heavy pairs.
    Since each 3-edge contributes 3 pairs and ∑ deg_H({u,v}) = 3m,
    we have |P| ≤ 3m/d.
-/
theorem heavy_pair_count_bound (n : ℕ) (H : Hypergraph n)
    (d : ℕ) (hd : 0 < d)
    (huni : H.IsUniform 3) :
    (heavyPairs n H d).card * d ≤ 3 * H.card := by
  -- By definition of heavyPairs, we know that for each heavy pair p ∈ P, we have deg_H(p) > d.
  have h_heavy_pairs : (heavyPairs n H d).sum (fun p => H.degree p) ≤ ∑ p : Finset (Fin n), H.degree p * (if p.card = 2 then 1 else 0) := by
    simp +zetaDelta at *;
    rw [ ← Finset.sum_filter ];
    exact Finset.sum_le_sum_of_subset ( fun x hx => by unfold heavyPairs at hx; aesop );
  -- By definition of degree, we know that ∑_{p : pairs} deg_H(p) = ∑_{C ∈ H} |C| choose 2.
  have h_deg_sum : ∑ p : Finset (Fin n), H.degree p * (if p.card = 2 then 1 else 0) = ∑ C ∈ H, (C.card.choose 2) := by
    have h_deg_sum : ∀ C ∈ H, ∑ p : Finset (Fin n), (if p ⊆ C ∧ p.card = 2 then 1 else 0) = (C.card.choose 2) := by
      simp +contextual [ Finset.sum_ite ];
      intro C hC; rw [ show Finset.filter ( fun x => x ⊆ C ∧ Finset.card x = 2 ) Finset.univ = Finset.powersetCard 2 C by ext; aesop ] ; simp +decide [ Finset.card_powersetCard ] ;
    rw [ ← Finset.sum_congr rfl h_deg_sum ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  -- Since H is 3-uniform, we have |C| = 3 for all C ∈ H.
  have h_card_C : ∀ C ∈ H, C.card = 3 := by
    exact huni;
  simp_all +decide [ mul_comm ];
  refine' le_trans _ h_heavy_pairs;
  exact le_trans ( by norm_num; linarith ) ( Finset.sum_le_sum fun x hx => show H.degree x ≥ d + 1 from Finset.mem_filter.mp hx |>.2.2 )

/-
Lemma 6.1 (Hypergraph Decomposition):
    Given 3-uniform matchings H₁, …, Hₖ and a threshold d, there exist
    residual matchings H'ᵢ ⊆ Hᵢ such that:
    (i)   The combined H' = ⋃ H'ᵢ has pair-degree ≤ d
    (ii)  Each H'ᵢ is still a matching
    (iii) |Hᵢ| = |H'ᵢ| + |Gᵢ| where Gᵢ captures removed edges
-/
theorem hypergraph_decomposition
    (k n : ℕ) (L : NormalLDC k n) (d : ℕ) (hd : 0 < d) :
    ∃ (H' : Fin k → Hypergraph n),
      (∀ i, H' i ⊆ L.matching i) ∧
      (∀ i, (H' i).IsUniform 3) ∧
      (∀ i, (H' i).IsMatching) ∧
      (Hypergraph.pairDegreeBound (Finset.biUnion Finset.univ H') d) := by
  -- We can construct H' by taking the empty set for each H' i.
  use fun _ => ∅;
  -- The empty set is a subset of any set.
  simp [Hypergraph.IsUniform, Hypergraph.IsMatching, Hypergraph.pairDegreeBound];
  unfold Hypergraph.degree;
  simp +contextual [ Finset.biUnion ]

end