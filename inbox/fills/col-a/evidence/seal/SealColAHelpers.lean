import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Simulator
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Closeness
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option autoImplicit false

/-! Rule-10 seal of col-a's helper modules: verbatim copies of `ColRepWitness.lean` and
`ColRepSound.lean` (namespace `SealA.ColRep`), with every foreign TCSlib definition their
elaborated terms mention sealed (`attribute [local irreducible]`), as found by `SealScan.lean`. -/

-- ===== copy of ColRepWitness.lean =====
namespace TCSlib.Cryptography.SealA.ColRep

attribute [local irreducible] _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.ColMachines.colorVal _root_.TCSlib.Cryptography.ColMachines.countTrue _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.L3COL _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.ProperColoring _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.R3COL _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.ThreeColorable _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decGraphAt _root_.TCSlib.Cryptography.edgeIdxOfMsg _root_.TCSlib.Cryptography.edgeMsg _root_.TCSlib.Cryptography.edgeOf _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.instDecidableProperColoring _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.sampleEdgeIdx _root_.TCSlib.Cryptography.samplePerm3 _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode


open Complexity Turing TCSlib.Cryptography.EncodingMachines TCSlib.Cryptography.ColMachines

/-! ### The decoded vertex count -/

/-- The vertex count of the graph decoded from `x` is `√|x|` (`GIZK.decGraph_eq_of_sqrt`). -/
theorem decGraph_fst (x : List Bool) : (decGraph x).1 = Nat.sqrt x.length :=
  congrArg Sigma.fst (GIZK.decGraph_eq_of_sqrt rfl)

/-! ### The decider -/

/-- The decider of `R_3COL` [PS10, §4.7, Definition 191.11 for `3COL`] (Def-124.f): on `⟨x, y⟩`,
`[x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c]` with `⟨n, G⟩ = decGraph x` and
`c = decColoring n y`. -/
def r3colTest (z : List Bool) : Bool :=
  decide (pairFstD z = encGraph (decGraph (pairFstD z)).2 ∧
    pairSndD z = encColoring (decColoring (decGraph (pairFstD z)).1 (pairSndD z)) ∧
    ProperColoring (decGraph (pairFstD z)).2 (decColoring (decGraph (pairFstD z)).1 (pairSndD z)))

/-- The defining equation of `r3colTest`: `[x = encGraph G ∧ y = encColoring c ∧
ProperColoring G c]` for `x = fst z`, `y = snd z`, `⟨n, G⟩ = decGraph x`, `c = decColoring n y`. -/
theorem r3colTest_eq (z : List Bool) :
    r3colTest z = decide (pairFstD z = encGraph (decGraph (pairFstD z)).2 ∧
      pairSndD z = encColoring (decColoring (decGraph (pairFstD z)).1 (pairSndD z)) ∧
      ProperColoring (decGraph (pairFstD z)).2
        (decColoring (decGraph (pairFstD z)).1 (pairSndD z))) := rfl

/-- **The decider of `R_3COL` is correct** [PS10, §4.7] (Def-124.f):
`r3colTest ⟨x, y⟩ = true ↔ R3COL x y`.

**Proof sketch.** (→) The decoded graph, its vertex count and the decoded colouring witness
`R3COL_iff`. (←) For `x = encGraph G`, `y = encColoring c`, `decGraph x = ⟨n, G⟩`
(`decGraph_encGraph`) and `decColoring n y = c` (`decColoring_encColoring`), so the three
conjuncts are `rfl`, `rfl` and the properness of `c`. -/
theorem r3colTest_iff (x y : List Bool) : r3colTest (pairEncode x y) = true ↔ R3COL x y := by
  rw [r3colTest_eq, pairFstD_pairEncode, pairSndD_pairEncode, decide_eq_true_iff, R3COL_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(decGraph x).1, (decGraph x).2, decColoring (decGraph x).1 y, h1, h2, h3⟩
  · rintro ⟨n, G, c, rfl, rfl, hc⟩
    have key : ∀ s : Σ n, Graph n, s = ⟨n, G⟩ → (encGraph G = encGraph s.2 ∧
        encColoring c = encColoring (decColoring s.1 (encColoring c)) ∧
        ProperColoring s.2 (decColoring s.1 (encColoring c))) := by
      intro s hs
      subst hs
      exact ⟨rfl, by rw [decColoring_encColoring], by rw [decColoring_encColoring]; exact hc⟩
    exact key _ (decGraph_encGraph G)

/-! ### The scan form -/

/-- Vertex `i` of the word `y` is badly encoded: bit `2i` or bit `2i + 1` differs from the
corresponding bit `[a / 2 = 1]`, `[a % 2 = 1]` of the colour value `a = colorVal y i`. -/
private def badVertex (y : List Bool) (i : ℕ) : Bool :=
  (y.getD (2 * i) false ^^ decide (colorVal y i / 2 = 1)) ||
    (y.getD (2 * i + 1) false ^^ decide (colorVal y i % 2 = 1))

/-- Position `j` of the `n × n` matrix `x` is a monochromatic edge for the colour values of `y`:
it is set and its endpoints `j / n`, `j % n` have equal colour values. -/
private def badEntry (x y : List Bool) (n j : ℕ) : Bool :=
  x.getD j false && decide (colorVal y (j / n) = colorVal y (j % n))

/-- The scan form of the decider on `x`, `y`, with `n = √|x|`: `|x| = n²`, `|y| = 2n`, no badly
encoded vertex below `n`, no monochromatic edge below `n²`. -/
private noncomputable def scanTest (x y : List Bool) : Bool :=
  decide (x.length = Nat.sqrt x.length * Nat.sqrt x.length) &&
    decide (y.length = Nat.sqrt x.length * 2) &&
    decide (firstIdx (badVertex y) (Nat.sqrt x.length) = Nat.sqrt x.length) &&
    decide (firstIdx (badEntry x y (Nat.sqrt x.length)) (Nat.sqrt x.length * Nat.sqrt x.length) =
      Nat.sqrt x.length * Nat.sqrt x.length)

/-- Exclusive or of two one-bit tests is polynomial-time (private copy of
`Complexity.polyTimeComputable_xor` of `Complexity/ClassP/BinaryArith/Basic.lean`, which is
not upstream of this file: `polyTimeComputable_ite` on the first test). -/
private theorem colRep_xor_poly {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x ^^ q x]) :=
  ptc_congr (polyTimeComputable_ite hp (polyTimeComputable_not hq) hq) fun x => by
    cases p x <;> cases q x <;> rfl

/-- Two Booleans with exclusive or `false` are equal. -/
private theorem eq_of_xor_eq_false {a b : Bool} (h : (a ^^ b) = false) : a = b := by
  revert h
  cases a <;> cases b <;> decide

/-- The well-formedness test as a length test: `x = encGraph G` for `⟨n, G⟩ = decGraph x` iff
`|x| = (√|x|)²` (`encGraph_decGraph_eq_take`, `decGraph_fst`, `Nat.sqrt_le`). -/
private theorem wf_iff (x : List Bool) :
    x = encGraph (decGraph x).2 ↔ x.length = Nat.sqrt x.length * Nat.sqrt x.length := by
  rw [encGraph_decGraph_eq_take, decGraph_fst]
  constructor
  · intro h
    have h1 := congrArg List.length h
    rw [List.length_take] at h1
    have h2 := Nat.sqrt_le x.length
    omega
  · intro h
    exact (List.take_of_length_le h.le).symm

/-- The colouring test: `y` is the encoding of the colouring it decodes to on `N` vertices iff
`|y| = 2N` and no vertex below `N` is badly encoded.

**Proof sketch.** Bits `2i`, `2i + 1` of the re-encoding are the bits of the colour value
`colorVal y i` (`getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one`,
`decColoring_val`). (→) Rewrite `y` by the hypothesis in those bits: every exclusive or vanishes.
(←) Compare the two lists entrywise (`List.ext_getElem`) at `k = 2i` and `k = 2i + 1`, `i < N`,
where a vanishing exclusive or (`firstIdx_eq_iff`) gives the equality of the bits. -/
private theorem enc_iff {N n : ℕ} (hn : N = n) (y : List Bool) :
    y = encColoring (decColoring N y) ↔ y.length = n * 2 ∧ firstIdx (badVertex y) n = n := by
  subst hn
  have hbit0 : ∀ i (hi : i < N), (encColoring (decColoring N y)).getD (2 * i) false =
      decide (colorVal y i / 2 = 1) := by
    intro i hi
    have h := getD_encColoring_two_mul (decColoring N y) ⟨i, hi⟩
    rw [decColoring_val] at h
    exact h
  have hbit1 : ∀ i (hi : i < N), (encColoring (decColoring N y)).getD (2 * i + 1) false =
      decide (colorVal y i % 2 = 1) := by
    intro i hi
    have h := getD_encColoring_two_mul_add_one (decColoring N y) ⟨i, hi⟩
    rw [decColoring_val] at h
    exact h
  constructor
  · intro h
    refine ⟨by rw [h, length_encColoring], firstIdx_eq_iff.2 fun i hi => ?_⟩
    have h0 := hbit0 i hi
    have h1 := hbit1 i hi
    rw [← h] at h0 h1
    rw [badVertex, h0, h1, Bool.xor_self, Bool.xor_self, Bool.or_false]
  · rintro ⟨hlen, hbad⟩
    have hgood := firstIdx_eq_iff.1 hbad
    have hlen' : (encColoring (decColoring N y)).length = y.length := by
      rw [length_encColoring, hlen]
    apply List.ext_getElem hlen'.symm
    intro k hk _
    obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
    · have hi : i < N := by omega
      have hb := hgood i hi
      rw [badVertex, Bool.or_eq_false_iff] at hb
      rw [← List.getD_eq_getElem _ false, ← List.getD_eq_getElem _ false, hbit0 i hi]
      exact eq_of_xor_eq_false hb.1
    · have hi : i < N := by omega
      have hb := hgood i hi
      rw [badVertex, Bool.or_eq_false_iff] at hb
      rw [← List.getD_eq_getElem _ false, ← List.getD_eq_getElem _ false, hbit1 i hi]
      exact eq_of_xor_eq_false hb.2

/-- The properness test: for a graph `G` on `N` vertices whose entry `(u, v)` is bit `v + N u`
of `x`, the decoded colouring is proper iff no position below `N²` is a monochromatic edge.

**Proof sketch.** Colours are compared through their values (`decColoring_val`, `Fin.ext`).
(→) A set position `j < N²` is the edge `(j / N, j % N)` (`Nat.mod_add_div`), whose colours
differ (`ProperColoring_iff`). (←) An edge `(u, v)` is position `v + N u < N²`, whose quotient
and remainder by `N` are `u` and `v`, and which is not monochromatic (`firstIdx_eq_iff`). -/
private theorem proper_iff {N n : ℕ} (hn : N = n) (G : Graph N) (x y : List Bool)
    (hG : ∀ u v : Fin N, G u v = x.getD (v + N * u) false) :
    ProperColoring G (decColoring N y) ↔ firstIdx (badEntry x y n) (n * n) = n * n := by
  subst hn
  rw [ProperColoring_iff, firstIdx_eq_iff]
  constructor
  · intro h j hj
    have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hj; omega
    have hu : j / N < N := Nat.div_lt_of_lt_mul hj
    have hv : j % N < N := Nat.mod_lt _ hN
    rw [badEntry, Bool.and_eq_false_iff]
    by_contra hcon
    push_neg at hcon
    simp only [ne_eq, Bool.not_eq_false, decide_eq_true_eq] at hcon
    have hadj : G ⟨j / N, hu⟩ ⟨j % N, hv⟩ = true := by
      rw [hG]
      have : j % N + N * (j / N) = j := Nat.mod_add_div j N
      rw [this]
      exact hcon.1
    refine h _ _ hadj (Fin.ext ?_)
    rw [decColoring_val, decColoring_val]
    exact hcon.2
  · intro h u v huv heq
    have hj : (v : ℕ) + N * u < N * N := by
      have := u.isLt
      have := v.isLt
      nlinarith
    have hb := h _ hj
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) u.isLt
    have hdiv : ((v : ℕ) + N * u) / N = u := by
      rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt v.isLt, zero_add]
    have hmod : ((v : ℕ) + N * u) % N = v := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
    rw [badEntry, hdiv, hmod, ← hG, huv, Bool.true_and, decide_eq_false_iff_not] at hb
    apply hb
    rw [← decColoring_val N y u, ← decColoring_val N y v, heq]

/-- The scan form agrees with the decider (`wf_iff`, `enc_iff`, `proper_iff` with
`decGraph_fst` and `decGraph_apply`). -/
private theorem scanTest_iff (x y : List Bool) :
    scanTest x y = true ↔ (x = encGraph (decGraph x).2 ∧
      y = encColoring (decColoring (decGraph x).1 y) ∧
      ProperColoring (decGraph x).2 (decColoring (decGraph x).1 y)) := by
  have hG : ∀ u v : Fin (decGraph x).1,
      (decGraph x).2 u v = x.getD (v + (decGraph x).1 * u) false := by
    intro u v
    rw [decGraph_apply, finProdFinEquiv_apply_val]
  rw [wf_iff, enc_iff (decGraph_fst x), proper_iff (decGraph_fst x) _ x y hG]
  simp only [scanTest, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ### Polynomial time -/

/-- The badly-encoded-vertex test is polynomial-time on `⟨1^i, z⟩` for `y = snd z`
(`getBit_poly`, `colorVal_poly`, `divNum_poly`, `modNum_poly`, `eqTest_poly`). -/
private theorem badVertex_poly :
    PolyTimeComputable fun w => [badVertex (pairSndD (pairSndD w)) (pairFstD w).length] := by
  have hY : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    ptc_comp polyTimeComputable_pairSndD polyTimeComputable_pairSndD
  have hI := unaryLength_poly polyTimeComputable_pairFstD
  have h2I := unaryMul_poly (unaryConst_poly 2) hI
  have hcv := colorVal_poly hY hI
  have hb0 := getBit_poly hY h2I
  have hb1 := getBit_poly hY (unaryAdd_poly h2I (unaryConst_poly 1))
  have hd0 := eqTest_poly (divNum_poly hcv (unaryConst_poly 2)) (unaryConst_poly 1)
  have hd1 := eqTest_poly (modNum_poly hcv (unaryConst_poly 2)) (unaryConst_poly 1)
  refine ptc_congr (polyTimeComputable_or (colRep_xor_poly hb0 hd0)
    (colRep_xor_poly hb1 hd1)) fun w => ?_
  rw [badVertex, divNum_eq, modNum_eq]

/-- The monochromatic-edge test is polynomial-time on `⟨1^j, z⟩` for `x = fst z`, `y = snd z`,
`n = √|x|` (`getBit_poly`, `unarySqrt_poly`, `divNum_poly`, `modNum_poly`, `colorVal_poly`,
`eqTest_poly`). -/
private theorem badEntry_poly :
    PolyTimeComputable fun w => [badEntry (pairFstD (pairSndD w)) (pairSndD (pairSndD w))
      (Nat.sqrt (pairFstD (pairSndD w)).length) (pairFstD w).length] := by
  have hX : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    ptc_comp polyTimeComputable_pairFstD polyTimeComputable_pairSndD
  have hY : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    ptc_comp polyTimeComputable_pairSndD polyTimeComputable_pairSndD
  have hI := unaryLength_poly polyTimeComputable_pairFstD
  have hn := unarySqrt_poly (unaryLength_poly hX)
  have hbit := getBit_poly hX hI
  have heq := eqTest_poly (colorVal_poly hY (divNum_poly hI hn)) (colorVal_poly hY (modNum_poly hI hn))
  refine ptc_congr (polyTimeComputable_and hbit heq) fun w => ?_
  rw [badEntry, divNum_eq, modNum_eq]

/-- The scan form is polynomial-time on `z = ⟨x, y⟩` (`polyTimeComputable_firstIdx` over
`badVertex_poly` and `badEntry_poly`, `eqTest_poly`, `polyTimeComputable_and`). -/
private theorem scanTest_poly :
    PolyTimeComputable fun z => [scanTest (pairFstD z) (pairSndD z)] := by
  have hX := unaryLength_poly polyTimeComputable_pairFstD
  have hY := unaryLength_poly polyTimeComputable_pairSndD
  have hn := unarySqrt_poly hX
  have hnn := unaryMul_poly hn hn
  have t1 := eqTest_poly hX hnn
  have t2 := eqTest_poly hY (unaryMul_poly hn (unaryConst_poly 2))
  have t3 := eqTest_poly (polyTimeComputable_firstIdx
    (p := fun z i => badVertex (pairSndD z) i) badVertex_poly hn) hn
  have t4 := eqTest_poly (polyTimeComputable_firstIdx
    (p := fun z j => badEntry (pairFstD z) (pairSndD z) (Nat.sqrt (pairFstD z).length) j)
    badEntry_poly hnn) hnn
  exact ptc_congr (polyTimeComputable_and (polyTimeComputable_and
    (polyTimeComputable_and t1 t2) t3) t4) fun z => rfl

/-- **The decider of `R_3COL` is polynomial-time** [PS10, Definition 191.11 for `3COL`]
(Def-124.f).

**Proof sketch.** Pointwise equal to the scan form (`scanTest_iff`, `r3colTest_eq`): `|x| = n²`,
`|y| = 2n`, and two bounded searches finding no badly encoded vertex below `n` and no
monochromatic edge below `n²` (`firstIdx_eq_iff`), each test a combination of `getBit_poly`,
`colorVal_poly` and unary arithmetic, the searches by `polyTimeComputable_firstIdx`. -/
theorem r3colTest_poly : PolyTimeComputable fun z => [r3colTest z] := by
  refine ptc_congr scanTest_poly fun z => ?_
  congr 1
  rw [Bool.eq_iff_iff, r3colTest_eq, decide_eq_true_iff, scanTest_iff]

/-- **The decider clause of `R3COL_witnessRelation`** [PS10, Definition 191.11 for `3COL`]
(Def-124.f): a polynomial-time `T` with `T ⟨x, y⟩ = true ↔ R3COL x y` (`r3colTest`,
`r3colTest_poly`, `r3colTest_iff`). -/
theorem R3COL_decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R3COL x y :=
  ⟨r3colTest, r3colTest_poly, r3colTest_iff⟩

end TCSlib.Cryptography.SealA.ColRep

-- ===== copy of ColRepSound.lean =====
namespace TCSlib.Cryptography.SealA.ColRep

attribute [local irreducible] _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.ColMachines.colorVal _root_.TCSlib.Cryptography.ColMachines.countTrue _root_.TCSlib.Cryptography.EncodingMachines.divNum _root_.TCSlib.Cryptography.EncodingMachines.firstIdx _root_.TCSlib.Cryptography.EncodingMachines.modNum _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.L3COL _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.ProperColoring _root_.TCSlib.Cryptography.Protocol.ProverBounded _root_.TCSlib.Cryptography.Protocol.outV _root_.TCSlib.Cryptography.Protocol.withV _root_.TCSlib.Cryptography.R3COL _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.Strategy.coinLen _root_.TCSlib.Cryptography.ThreeColorable _root_.TCSlib.Cryptography.decColoring _root_.TCSlib.Cryptography.decGraph _root_.TCSlib.Cryptography.decGraphAt _root_.TCSlib.Cryptography.edgeIdxOfMsg _root_.TCSlib.Cryptography.edgeMsg _root_.TCSlib.Cryptography.edgeOf _root_.TCSlib.Cryptography.encColoring _root_.TCSlib.Cryptography.encGraph _root_.TCSlib.Cryptography.exec _root_.TCSlib.Cryptography.instDecidableProperColoring _root_.TCSlib.Cryptography.moverIsV _root_.TCSlib.Cryptography.sampleEdgeIdx _root_.TCSlib.Cryptography.samplePerm3 _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode


open Complexity Turing

/-! ### The prover's view against a challenge verifier -/

/-- The prover's view after `i` iterations against a verifier that sends the challenge `ch j`
and then the empty message in iteration `j`: `[ch 0, [], ch 1, [], …, ch (i-1), []]`. -/
def chView (ch : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => chView ch i ++ [ch i, []]

/-- `chView ch 0 = []`. -/
theorem chView_zero (ch : ℕ → List Bool) : chView ch 0 = [] := rfl

/-- `chView ch (i + 1) = chView ch i ++ [ch i, []]`. -/
theorem chView_succ (ch : ℕ → List Bool) (i : ℕ) : chView ch (i + 1) = chView ch i ++ [ch i, []] :=
  rfl

/-- The prover's view after `i` iterations has `2i` messages. -/
theorem length_chView (ch : ℕ → List Bool) : ∀ i, (chView ch i).length = 2 * i
  | 0 => rfl
  | i + 1 => by
    rw [chView_succ, List.length_append, length_chView ch i]
    rfl

/-- The prover's view after `i` iterations depends only on the first `i` challenges. -/
theorem chView_congr {f g : ℕ → List Bool} : ∀ i, (∀ k < i, f k = g k) → chView f i = chView g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [chView_succ, chView_succ, chView_congr i (fun k hk => h k (by omega)), h i (by omega)]

/-- **Four-move iterations against a challenge verifier** [PS10, Protocol 127.5, repeated]: in
the prover-first execution `P'_{rP}(x, y) ↔ V_{rV}(x, z)`, if `V` answers every odd history of
`2j + 1` messages with `ch j` and every even history of fewer than `2N` messages with `[]`,
then for `i ≤ N` after `4i` moves the verifier has received `2i` messages, message `2j` being
`P'(chView ch j)` and message `2j + 1` being `P'(chView ch j ++ [ch j])` for `j < i`, and, if
`i < N`, the prover has received `chView ch i`.

**Proof sketch.** Induction on `i`: four applications of `exec_succ` (`moverIsV_false`: the
prover moves at `4i`, `4i + 2`); the challenge is `ch i` (`hodd` on `2i + 1` messages) and the
fourth message is `[]` while `2i + 2 < 2N` (`hmid`); the new messages are appended at the end
(`List.getD_append`, `List.getD_append_right`). -/
theorem exec_four_mul (P' V : Strategy) (x y z rP rV : List Bool) (ch : ℕ → List Bool) (N : ℕ)
    (hodd : ∀ hist : List (List Bool), hist.length % 2 = 1 →
      V.next x z rV hist = ch (hist.length / 2))
    (hmid : ∀ hist : List (List Bool), hist.length % 2 = 0 → hist.length < 2 * N →
      V.next x z rV hist = []) :
    ∀ i, i ≤ N → (exec P' V false x y z rP rV (4 * i)).2.length = 2 * i ∧
      (∀ j < i, (exec P' V false x y z rP rV (4 * i)).2.getD (2 * j) [] =
          P'.next x y rP (chView ch j) ∧
        (exec P' V false x y z rP rV (4 * i)).2.getD (2 * j + 1) [] =
          P'.next x y rP (chView ch j ++ [ch j])) ∧
      (i < N → (exec P' V false x y z rP rV (4 * i)).1 = chView ch i)
  | 0, _ => by
    rw [Nat.mul_zero, exec_zero]
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ => (chView_zero ch).symm⟩
  | i + 1, hi => by
    obtain ⟨hlen, hget, hP⟩ := exec_four_mul P' V x y z rP rV ch N hodd hmid i (by omega)
    have hPi := hP (by omega)
    have h0 : moverIsV false (4 * i) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h1 : moverIsV false (4 * i + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    have h2 : moverIsV false (4 * i + 1 + 1) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h3 : moverIsV false (4 * i + 1 + 1 + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    set E := exec P' V false x y z rP rV (4 * i) with hE
    have hstep : exec P' V false x y z rP rV (4 * (i + 1)) =
        (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1]),
            V.next x z rV (E.2 ++ [P'.next x y rP E.1,
              P'.next x y rP (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1])])])],
          E.2 ++ [P'.next x y rP E.1,
            P'.next x y rP (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1])])]) := by
      rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by ring, exec_succ, exec_succ, exec_succ,
        exec_succ, ← hE]
      simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, List.append_assoc,
        List.singleton_append]
    have hb : V.next x z rV (E.2 ++ [P'.next x y rP E.1]) = ch i := by
      rw [hodd _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
        List.length_append, hlen, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    rw [hstep, hb, hPi]
    refine ⟨?_, fun j hj => ?_, fun hN => ?_⟩
    · rw [List.length_append, hlen]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hget j hj'
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hlen, Nat.sub_self, show 2 * j + 1 - 2 * j = 1 by omega]
        exact ⟨rfl, rfl⟩
    · rw [hmid _ (by rw [List.length_append, hlen, List.length_cons, List.length_singleton]; omega)
        (by rw [List.length_append, hlen, List.length_cons, List.length_singleton]; omega),
        chView_succ]

/-! ### Blocks of a tape -/

/-- The first `K` blocks of `b` bits of a tape of `C ≥ K b` bits: bit `j` of block `t` is bit
`t b + j` of the tape. -/
def blockRead (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) (j : Fin b) : Bool :=
  r ⟨t * b + j, by
    calc (t : ℕ) * b + j < (t : ℕ) * b + b := by omega
      _ = ((t : ℕ) + 1) * b := by ring
      _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
      _ ≤ C := h⟩

/-- The defining equation of `blockRead`: bit `j` of block `t` is bit `t b + j` of the tape. -/
theorem blockRead_eq (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) (j : Fin b) :
    blockRead b K C h r t j = r ⟨t * b + j, by
      calc (t : ℕ) * b + j < (t : ℕ) * b + b := by omega
        _ = ((t : ℕ) + 1) * b := by ring
        _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
        _ ≤ C := h⟩ := rfl

/-- **The blocks of a uniform tape are independent and uniform**: `blockRead` is the restriction
to the first `K b` bits (`GIZK.pushesUniform_castLE`) followed by the bijection
`(Fin (K b) → Bool) ≃ (Fin K → Fin b → Bool)` (`finProdFinEquiv`, `Equiv.curry`). -/
theorem pushesUniform_blockRead (b K C : ℕ) (h : K * b ≤ C) :
    HardcoreBit.PushesUniform (blockRead b K C h) := by
  let e : (Fin (K * b) → Bool) ≃ (Fin K → Fin b → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  have he : ∀ s : Fin (K * b) → Bool, ∀ t j, e s t j = s (finProdFinEquiv (t, j)) := by
    intro s t j
    rfl
  have hc := (GIZK.pushesUniform_castLE (B := Bool) h).comp (HardcoreBit.pushesUniform_equiv e)
  convert hc using 1
  funext r t j
  rw [he, blockRead_eq]
  congr 1
  apply Fin.ext
  simp only [Fin.coe_castLE, finProdFinEquiv_apply_val]
  ring

/-- The list slice of block `t` of a tape is the list of the block:
`((List.ofFn r).drop (t b)).take b = List.ofFn (blockRead b K C h r t)`. -/
theorem drop_take_ofFn_blockRead (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) :
    ((List.ofFn r).drop (t * b)).take b = List.ofFn (blockRead b K C h r t) := by
  have hle : (t : ℕ) * b + b ≤ C := by
    calc (t : ℕ) * b + b = ((t : ℕ) + 1) * b := by ring
      _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
      _ ≤ C := h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn, blockRead_eq]

/-! ### Independent edge samplers -/

/-- **`K` rejection-sampled edge indices are close to uniform** [PS10, Protocol 127.5 with the
sampler of D10]: on a uniform tape of `C ≥ K b` bits, the edge indices `sampleEdgeIdx m T` of
the first `K` blocks of `b ≥ T ⌈log m⌉` bits are `K (1/2)^T`-close to `K` independent uniform
indices in `[m]`.

**Proof sketch.** One block: `statClose_sampleEdgeIdx` on the first `T · size m` bits of the
block (`GIZK.pushesUniform_castLE`, `ColProofs.sampleEdgeIdx_ofFn_castLE`); `K` blocks:
`OneWay.statClose_pi`; the tape: `pushesUniform_blockRead` (`StatClose.comp_pushesUniform`). -/
theorem statClose_edgeBlocks {m : ℕ} (hm : 0 < m) (T b K C : ℕ) (hb : T * Nat.size m ≤ b)
    (h : K * b ≤ C) :
    StatClose (fun r : Fin C → Bool => fun t : Fin K =>
        (⟨sampleEdgeIdx m T (List.ofFn (blockRead b K C h r t)), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : (Fin K → Fin m) → Fin K → Fin m) (K * (1 / 2 : ℝ) ^ T) := by
  have h1 : StatClose (fun g : Fin b → Bool =>
      (⟨sampleEdgeIdx m T (List.ofFn g), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : Fin m → Fin m) ((1 / 2 : ℝ) ^ T) := by
    have h0 := (statClose_sampleEdgeIdx hm T).comp_pushesUniform
      (GIZK.pushesUniform_castLE (B := Bool) hb)
    convert h0 using 2 with g
    exact Fin.ext (ColProofs.sampleEdgeIdx_ofFn_castLE hb g)
  exact (OneWay.statClose_pi h1 K).comp_pushesUniform (pushesUniform_blockRead b K C h)

/-! ### The number of iterations -/

/-- On an encoded graph `n |E| ≤ |x|²`: `|E| ≤ n²` (`ColMachines.edgeCount_eq`,
`ColMachines.countTrue_le`) and `n · n² ≤ n⁴` (the `n|E|` iterations of the repeated protocol fit in
its `|x|²` slots, [PS10, Protocol 127.5]). -/
theorem mul_edgeCount_le {n : ℕ} (G : Graph n) :
    n * edgeCount G ≤ (encGraph G).length * (encGraph G).length := by
  have hm : edgeCount G ≤ n * n := by
    rw [ColMachines.edgeCount_eq G (encGraph G) fun u v => (encGraph_getD G u v).symm]
    exact ColMachines.countTrue_le _ _
  rw [length_encGraph]
  calc n * edgeCount G ≤ n * (n * n) := Nat.mul_le_mul_left n hm
    _ ≤ n * n * (n * n) := Nat.mul_le_mul_right (n * n) (Nat.le_mul_self n)

end TCSlib.Cryptography.SealA.ColRep
