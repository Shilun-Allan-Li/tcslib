## TCSlib/Complexity/ClassNP/SAT.lean · sat_guard_add

4043: private lemma sat_guard_add {k : ℕ} {S : Type} {x : List Bool}
4044:     (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
4045:     (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
4046:     (he : tm.runFrom c a = d)
4047:     (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
4048:     ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
4049:   have h₁ : Turing.Segment tm {some anchor} (fun _ => True) c d a :=
4050:     (Turing.segment_iff tm {some anchor} (fun _ => True) c d a).mpr
4051:       ⟨he, fun v hv hm => ha v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
4052:   have h₂ : Turing.Segment tm {some anchor} (fun _ => True) d (tm.runFrom d b) b :=
4053:     (Turing.segment_iff tm {some anchor} (fun _ => True) d (tm.runFrom d b) b).mpr
4054:       ⟨rfl, fun v hv hm => hb v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
4055:   have h := (Turing.segment_iff tm {some anchor} (fun _ => True) c (tm.runFrom d b)
4056:     (a + b)).mp (Turing.Segment.trans h₁ h₂)
4057:   intro v hv hm
4058:   exact h.2.1 v hv (Set.mem_singleton_iff.mpr hm)
4059: 

## TCSlib/Complexity/ClassNP/SAT.lean · sat_pt_pair_input

2714: private lemma sat_pt_pair_input {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
2715:     PolyTimeComputable (fun x => pairEncode (f x) x) := by
2716:   exact PolyTimeComputable.pairEncode hf polyTimeComputable_id
2717: 

## TCSlib/Complexity/ClassNP/SAT.lean · sat_pt_mapSnd

2720: private lemma sat_pt_mapSnd {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
2721:     PolyTimeComputable (fun z => match pairDecode z with
2722:       | some (a, b) => pairEncode a (g b)
2723:       | none => []) := by
2724:   have he : Complexity.pairMapSnd g = (fun z => match pairDecode z with
2725:       | some (a, b) => pairEncode a (g b)
2726:       | none => []) := funext (Complexity.pairMapSnd.eq_1 g)
2727:   rw [← he]
2728:   exact PolyTimeComputable.pairMapSnd hg
2729: 

## TCSlib/Complexity/ClassNP/SAT.lean · sat_pt_pair

2732: private lemma sat_pt_pair {f g : List Bool → List Bool}
2733:     (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
2734:     PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
2735:   exact PolyTimeComputable.pairEncode hf hg
2736: 

## TCSlib/Complexity/ClassNP/SAT.lean · sat_pt_append

2738: private lemma sat_pt_append {f g : List Bool → List Bool}
2739:     (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
2740:     PolyTimeComputable (fun x => f x ++ g x) := by
2741:   exact PolyTimeComputable.append hf hg
2742: 

## TCSlib/Complexity/ClassNP/SAT.lean · sat_pt_unaryLength

2820: private lemma sat_pt_unaryLength : PolyTimeComputable (fun x => List.replicate x.length true) := by
2821:   exact polyTimeComputable_unary
2822: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5_guard_add

6367: private lemma clA5_guard_add {k : ℕ} {S : Type} {x : List Bool}
6368:     (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
6369:     (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
6370:     (he : tm.runFrom c a = d)
6371:     (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
6372:     ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
6373:   have h₁ : Turing.Segment tm {some anchor} (fun _ => True) c d a :=
6374:     (Turing.segment_iff tm {some anchor} (fun _ => True) c d a).mpr
6375:       ⟨he, fun v hv hm => ha v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
6376:   have h₂ : Turing.Segment tm {some anchor} (fun _ => True) d (tm.runFrom d b) b :=
6377:     (Turing.segment_iff tm {some anchor} (fun _ => True) d (tm.runFrom d b) b).mpr
6378:       ⟨rfl, fun v hv hm => hb v hv (Set.mem_singleton_iff.mp hm), fun _ _ => True.intro⟩
6379:   have h := (Turing.segment_iff tm {some anchor} (fun _ => True) c (tm.runFrom d b)
6380:     (a + b)).mp (Turing.Segment.trans h₁ h₂)
6381:   intro v hv hm
6382:   exact h.2.1 v hv (Set.mem_singleton_iff.mpr hm)
6383: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_linear

627: private lemma clNative_linear (f : List Bool → List Bool)
628:     (h : ∃ (M : FinTM Bool) (a : ℕ),
629:       M.ComputesFunInTime f (fun n => a * (n + 1))) : PolyTimeComputable f := by
630:   exact polyTimeComputable_of_linear h
631: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_map

634: private lemma clNative_map {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
635:     PolyTimeComputable (fun z => match pairDecode z with
636:       | some (a, b) => pairEncode a (g b)
637:       | none => []) := by
638:   have he : Complexity.pairMapSnd g = (fun z => match pairDecode z with
639:       | some (a, b) => pairEncode a (g b)
640:       | none => []) := funext (Complexity.pairMapSnd.eq_1 g)
641:   rw [← he]
642:   exact PolyTimeComputable.pairMapSnd hg
643: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_pair

646: private lemma clNative_pair {f g : List Bool → List Bool}
647:     (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
648:     PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
649:   exact PolyTimeComputable.pairEncode hf hg
650: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_append

653: private lemma clNative_append {f g : List Bool → List Bool}
654:     (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
655:     PolyTimeComputable (fun x => f x ++ g x) := by
656:   exact PolyTimeComputable.append hf hg
657: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_unary

660: private lemma clNative_unary (C e : ℕ) :
661:     PolyTimeComputable (fun x => List.replicate (C * (x.length + 1) ^ e) true) := by
662:   exact polyTimeComputable_polyUnary C e
663: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5_pt_const

6626: private lemma clA5_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
6627:   exact polyTimeComputable_const w
6628: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5_pt_cond

6631: private lemma clA5_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
6632:     (hp : PolyTimeComputable (fun x => [p x]))
6633:     (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
6634:     PolyTimeComputable (fun x => if p x then f x else g x) := by
6635:   exact polyTimeComputable_ite hp hf hg
6636: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5_pt_and

6638: private lemma clA5_pt_and {p q : List Bool → Bool}
6639:     (hp : PolyTimeComputable (fun x => [p x]))
6640:     (hq : PolyTimeComputable (fun x => [q x])) :
6641:     PolyTimeComputable (fun x => [p x && q x]) := by
6642:   exact polyTimeComputable_and hp hq
6643: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5Pair_sizes

6839: private lemma clA5Pair_sizes (w : List Bool) :
6840:     (clHeaderField 0 w).length ≤ w.length ∧ (clHeaderTail 1 w).length ≤ w.length := by
6841:   change (((pairDecode w).map Prod.fst).getD []).length ≤ w.length ∧
6842:     (((pairDecode w).map Prod.snd).getD []).length ≤ w.length
6843:   cases hd : pairDecode w with
6844:   | none =>
6845:     simp only [Option.map_none, Option.getD_none, List.length_nil]
6846:     exact ⟨Nat.zero_le _, Nat.zero_le _⟩
6847:   | some p =>
6848:     rcases p with ⟨a, b⟩
6849:     have heq := eq_pairEncode_of_pairDecode w a b hd
6850:     have hbound := length_pair_components_le w
6851:     have hab : 2 * a.length + b.length ≤ w.length := by
6852:       simpa only [heq, pairFstD_pairEncode, pairSndD_pairEncode] using hbound
6853:     simp only [Option.map_some, Option.getD_some]
6854:     constructor <;> omega
6855: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5Le_native

6883: private lemma clA5Le_native {f g : List Bool → ℕ}
6884:     (hf : PolyTimeComputable (fun x => List.replicate (f x) true))
6885:     (hg : PolyTimeComputable (fun x => List.replicate (g x) true)) :
6886:     PolyTimeComputable (fun x => [decide (f x ≤ g x)]) := by
6887:   have h := polyTimeComputable_lenLe.comp (hg.pairEncode hf)
6888:   convert h using 1
6889:   funext x
6890:   simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
6891:     List.length_replicate]
6892: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clA5Drop_native

6822: private lemma clA5Drop_native {s u : List Bool → List Bool}
6823:     (hs : PolyTimeComputable s) (hu : PolyTimeComputable u) :
6824:     PolyTimeComputable (fun x => (s x).drop (u x).length) := by
6825:   have h := polyTimeComputable_dropPrefixByLength.comp (hu.pairEncode hs)
6826:   have he : (PrefixByLength.drop ∘ (fun x => pairEncode (u x) (s x))) =
6827:       (fun x => (s x).drop (u x).length) := by
6828:     funext x
6829:     rw [Function.comp_apply, PrefixByLength.drop.eq_1,
6830:       pairFstD_pairEncode, pairSndD_pairEncode]
6831:   rw [he] at h
6832:   exact h
6833: 

## TCSlib/Complexity/CookLevin/Hardness.lean · clNative_image

5158: private lemma clNative_image {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
5159:     (B : FinTM Bool) (b r : ℕ)
5160:     (hB : ∀ x, B.ComputesInTime (f x) (g x) (b * ((f x).length + 1) ^ r)) :
5161:     PolyTimeComputable g := by
5162:   obtain ⟨A, a, d, hA⟩ := hf
5163:   refine ⟨FinTM.bufferedCompTM A B, 2 * a + b * (a + 1) ^ r + 2, d * (r + 1), ?_⟩
5164:   intro x
5165:   have hc := FinTM.bufferedCompTM_computesInTime A B (hA x) (hB x)
5166:   apply hc.mono
5167:   have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hA x)).2
5168:   have hlen : (f x).length ≤ a * (x.length + 1) ^ d := by
5169:     simpa only [ho] using A.tm.output_length_le x (a * (x.length + 1) ^ d)
5170:   have hpos : 1 ≤ (x.length + 1) ^ d := Nat.one_le_pow d _ (by omega)
5171:   have hword : (f x).length + 1 ≤ (a + 1) * (x.length + 1) ^ d := by rw [Nat.add_mul, Nat.one_mul]; omega
5172:   have hpow := Nat.pow_le_pow_left hword r
5173:   rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
5174:   have hd := Nat.pow_le_pow_right (Nat.succ_pos x.length)
5175:     (show d ≤ d * (r + 1) by rw [Nat.mul_add, Nat.mul_one]; omega)
5176:   have hdr := Nat.pow_le_pow_right (Nat.succ_pos x.length)
5177:     (show d * r ≤ d * (r + 1) by rw [Nat.mul_add, Nat.mul_one]; omega)
5178:   have hm := Nat.mul_le_mul_left ((a + 1) ^ r) hdr
5179:   have hcost := Nat.mul_le_mul_left b (hpow.trans hm)
5180:   have hfirst := Nat.mul_le_mul_left (2 * a) hd
5181:   have hlast : 1 ≤ (x.length + 1) ^ (d * (r + 1)) := Nat.one_le_pow _ _ (by omega)
5182:   calc
5183:     _ ≤ 2 * (a * (x.length + 1) ^ d) + b * ((f x).length + 1) ^ r + 2 := by
5184:       dsimp only
5185:       omega
5186:     _ ≤ (2 * a) * (x.length + 1) ^ (d * (r + 1)) +
5187:         (b * (a + 1) ^ r) * (x.length + 1) ^ (d * (r + 1)) +
5188:         2 * (x.length + 1) ^ (d * (r + 1)) := by
5189:       exact Nat.add_le_add (Nat.add_le_add
5190:         (by simpa only [Nat.mul_assoc] using hfirst)
5191:         (by simpa only [Nat.mul_assoc] using hcost)) (Nat.mul_le_mul_left 2 hlast)
5192:     _ = _ := by ring
5193: 

## TCSlib/Complexity/ClassNP/Tautology.lean · taut_comp_on_image

1052: private lemma taut_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
1053:     (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
1054:     (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
1055:     ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2*T₁ n+T₂ n+2) := by
1056:   exact FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU
1057: 

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean · Segment

424: def Segment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
425:     (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
426:   M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
427:     ∀ u ≤ t, P (M.runFrom a u).workTapePos
428: 

## TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean · segment_iff

432: theorem segment_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
433:     (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) :
434:     Segment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
435:       ∀ u ≤ t, P (M.runFrom a u).workTapePos :=
436:   Iff.rfl
437: 

## TCSlib/Complexity/ClassNP/PolyTime.lean · PolyTimeComputable

69: def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
70:   ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c
71: 

## TCSlib/Complexity/ClassNP/PolyTimePrefix.lean · drop

51: def drop (z : List Bool) : List Bool :=
52:   (pairSndD z).drop (pairFstD z).length
53: 
