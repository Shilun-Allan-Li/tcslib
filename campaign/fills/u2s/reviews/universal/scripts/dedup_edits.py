"""Apply the drafted dedup edits D1-D3 (cite exists_first_halt, visitedByTapeHead_mono and
ComputesInTime.spaceUsed_le_of_halt instead of re-deriving them). Usage: dedup_edits.py <in> <out>"""
import sys
src = open(sys.argv[1], encoding='utf-8').read()
edits = [
("D1", """  classical
  let hex : ∃ u, (M.runFrom (M.initCfg x) u).state = none := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have hle : t₀ ≤ t := Nat.find_min' hex hhalt
  have hfirst : ∀ u < t₀, (M.runFrom (M.initCfg x) u).state ≠ none :=
    fun u hu => Nat.find_min hex hu
  have hsame : M.runFrom (M.initCfg x) t₀ = M.runFrom (M.initCfg x) t := by
    symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
""", """  obtain ⟨t₀, hle, hfirst, hsame⟩ := MultiTapeTM.exists_first_halt M (M.initCfg x) hhalt
  refine ⟨t₀, hle, hfirst, ?_, ?_⟩
"""),
("D2", """          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card := Finset.card_le_card (by
            intro p hp
            rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hp ⊢
            obtain ⟨u, hu, hp⟩ := hp
            exact ⟨u, hu.trans ht₀, hp⟩)
""", """          _ ≤ (M.visitedByTapeHead (M.initCfg z) t j).card :=
            Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (M.initCfg z) ht₀ j)
"""),
("D3a", """    refine ⟨((FinTM.computesInTime_iff U z output (T + 1 + v)).mpr
      ⟨hUhalt, hUout⟩).mono htime, ?_⟩
""", """    have hUcomp : U.ComputesInTime z output (T + 1 + v) :=
      (FinTM.computesInTime_iff U z output (T + 1 + v)).mpr ⟨hUhalt, hUout⟩
    refine ⟨hUcomp.mono htime, ?_⟩
"""),
("D3b", """    have hfreeze : U.tm.spaceUsed (U.tm.initCfg z) (C * (t + 1)) ≤
        U.tm.spaceUsed (U.tm.initCfg z) (T + 1 + v) := by
      rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card]
      apply Finset.card_le_card
      intro p hp
      have splitVisits := MultiTapeTM.visitedByTapeHead_add_subset U.tm (U.tm.initCfg z)
        (T + 1 + v) (C * (t + 1) - (T + 1 + v)) j
      rw [Nat.add_sub_of_le htime] at splitVisits
      rcases Finset.mem_union.mp (splitVisits hp) with hpast | hfuture
      · exact hpast
      · rw [MultiTapeTM.mem_visitedByTapeHead_iff] at hfuture ⊢
        obtain ⟨u, _, he⟩ := hfuture
        rw [MultiTapeTM.runFrom_of_halt _ hUhalt] at he
        exact ⟨T + 1 + v, le_rfl, he⟩
    calc
      _ ≤ U.tm.spaceUsed (U.tm.initCfg z) (T + 1 + v) := hfreeze
      _ ≤ B + N * (s + (2 * D + 1)) := hspace
""", """    calc
      _ ≤ B + N * (s + (2 * D + 1)) :=
        FinTM.ComputesInTime.spaceUsed_le_of_halt hUcomp hspace _
"""),
]
for name, old, new in edits:
    n = src.count(old)
    assert n == 1, (name, n)
    src = src.replace(old, new)
    print(name, 'applied')
open(sys.argv[2], 'w', encoding='utf-8').write(src)
