"""Apply the review's landing edits E1-E6 to the head file; every replacement is asserted to occur
exactly once. usage: landing_edits.py <head.lean> <out.lean>"""
import sys
src = open(sys.argv[1], encoding='utf-8').read()
def rep(tag, old, new):
    global src
    n = src.count(old)
    assert n == 1, f'{tag}: {n} occurrences'
    src = src.replace(old, new)
    print(f'{tag}: applied')
# E1: qy_call_bound's hb cites Turing.length_bits_le_self (gate 87's finding 2; the landing's item)
rep('E1', '''  have hb : (Nat.bits (f a)).length ≤ f a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self)
''', '''  have hb := Turing.length_bits_le_self (f a)
''')
# E2: rule 10: no core definition passed to rw (Ne); its published equation ne_eq instead
rep('E2', '''        rw [Ne, compare_gt_iff_gt]''', '''        rw [ne_eq, compare_gt_iff_gt]''')
# E3: dz_padded_value cites Mathlib's Nat.ofDigits_append_replicate_zero instead of re-deriving it
rep('E3', '''/-- The zero-padded bits of `t` are worth `t`. -/
private theorem dz_padded_value (t r : ℕ) :
    Nat.ofDigits 2 ((Nat.bits t ++ List.replicate r false).map Bool.toNat) = t := by
  have h0 : ∀ r : ℕ, Nat.ofDigits 2 ((List.replicate r false).map Bool.toNat) = 0 := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [List.replicate_succ, List.map_cons, Nat.ofDigits_cons, ih]
      rfl
  rw [List.map_append, Nat.ofDigits_append, h0, mul_zero, add_zero, qy_bits_val]
''', '''/-- The zero-padded bits of `t` are worth `t` (`Nat.ofDigits_append_replicate_zero`). -/
private theorem dz_padded_value (t r : ℕ) :
    Nat.ofDigits 2 ((Nat.bits t ++ List.replicate r false).map Bool.toNat) = t := by
  rw [List.map_append, List.map_replicate, Bool.toNat_false, Nat.ofDigits_append_replicate_zero,
    qy_bits_val]
''')
# E4: dz_top_run's first halt cites Turing.MultiTapeTM.exists_first_halt instead of re-deriving it
rep('E4a', '''  · have h0 : ∃ τ, (BF.tm.runFrom c0 τ).state = none := by
      obtain ⟨τ, -, h⟩ := hh
      exact ⟨τ, h⟩
    set τ₀ := Nat.find h0 with hτ₀
    have hτ₀G : τ₀ ≤ G := by
      obtain ⟨τ, hτ, h⟩ := hh
      exact (Nat.find_min' h0 h).trans hτ
    have hst0 : (BF.tm.runFrom c0 τ₀).state = none := Nat.find_spec h0
    obtain ⟨t, ht, b, T', P', hrun, hcap, hpos, hcutH⟩ := hfin τ₀ hτ₀G ((hstopped τ₀).mpr hst0)
      (fun u hu h => Nat.find_min h0 hu ((hstopped u).mp h))
''', '''  · obtain ⟨τw, hτw, hstw⟩ := hh
    obtain ⟨τ₀, hτ₀w, hlive0, heq0⟩ := MultiTapeTM.exists_first_halt BF.tm c0 hstw
    have hτ₀G : τ₀ ≤ G := hτ₀w.trans hτw
    have hst0 : (BF.tm.runFrom c0 τ₀).state = none := by rw [heq0]; exact hstw
    obtain ⟨t, ht, b, T', P', hrun, hcap, hpos, hcutH⟩ := hfin τ₀ hτ₀G ((hstopped τ₀).mpr hst0)
      (fun u hu h => hlive0 u hu ((hstopped u).mp h))
''')
rep('E4b', '''    · have hle : τ₀ ≤ τ := Nat.find_min' h0 hstτ
''', '''    · have hle : τ₀ ≤ τ := Nat.le_of_not_lt fun hlt => hlive0 τ hlt hstτ
''')
rep('E4c', '''decider halts by `G`, at its first halt `τ₀` (`Nat.find`) the finish clause leaves its output on the
capture tape (at most `τ₀` symbols, `MultiTapeTM.output_length_le`); the dispatch rewinds it
''', '''decider halts by `G`, at its first halt `τ₀` (`Turing.MultiTapeTM.exists_first_halt`) the finish
clause leaves its output on the capture tape (at most `τ₀` symbols,
`MultiTapeTM.output_length_le`); the dispatch rewinds it
''')
# E5: public-facing text: "published" in the campaign's sense
rep('E5', '''(`Turing.NTimeDiag.exists_queryTM`), of `g`'s witness and of the published prepend row; the install
calls (`qy_installSpec`) of `computesFunInTime_lengthBits` and of the composite extractor
''', '''(`Turing.NTimeDiag.exists_queryTM`), of `g`'s witness and of the prepend row
(`Turing.FinTM.computesFunInTime_prepend`); the install calls (`qy_installSpec`) of
`computesFunInTime_lengthBits` and of the composite extractor
''')
# E6: the Implementation paragraph (the brief's landing item), REPORT's text, after the docstring's last paragraph
rep('E6', '''(`Turing.NDTM.runWith_mapState_of_agreeOn_det`); the clock's two exits per rung; the per-code
constant `C = max 1 (max C_R C_BF)`. -/
theorem exists_diagonalizer''', '''(`Turing.NDTM.runWith_mapState_of_agreeOn_det`); the clock's two exits per rung; the per-code
constant `C = max 1 (max C_R C_BF)`.

**Implementation.** `D` is `Turing.guessRunTM` over a deterministic setup and a deterministic
run. The setup calls the stage query, `g`'s witness and `x ↦ true :: x` on the native input
(released input calls), and writes the block `1^{g n} ++ [true] ++ bits (g n)` (two expansions and
a copy), the ruler `1^{g n}` and the clock's counter `bits (g n)`. The guess overwrites the block
with a stream, a separator and a budget word. The run is a phase host: a one-cell take reads the
query's flag; in the middle it splits the block (a skip back, the lockstep walk over the ruler, a
take of the separator, a move of the budget word), tests the budget `b ≤ g n` (its expansion and
the length comparison with the stream), normalizes it to `bits b` (an install call), extracts `α`
from the query's tail (the install call of the composite pair extractor), writes the core's input
`⟨⟨bits b, α⟩, 1^{n + 1}⟩` by three emissions under the capture wrapper, and runs the interpreter
core under the step clock over the virtual-input host, accepting at its `accept` within the
allowance `g n`; at a top it runs the decider of `hBF` on the query's tail under the same clocked
host and accepts iff its captured output starts with `false`. All-branch halting is
`Turing.guessRunTM_haltsWithin` and acceptance `Turing.guessRunTM_accepts_iff`; `K` is uniform and,
per code, `C = max 1 (max C_R C_BF)`. -/
theorem exists_diagonalizer''')
# E7: private docstrings: one inaccurate, four bare labels, restated as their statements
rep('E7a', '''/-- The query's first cell after its flag. -/''',
    '''/-- The buffer of `b :: tail` holds `b` at cell `0`: the query's flag, which the take reads. -/''')
rep('E7b', '''/-- A layout on a named tape. -/''',
    '''/-- A layout holds its named value on a named tape: `dzLay L d (κ.tp i) = L i`. -/''')
rep('E7c', '''/-- A layout off the named tapes. -/''',
    '''/-- A layout holds the default `d` on every tape of index at least `14`. -/''')
rep('E7d', '''/-- The value of a named tape. -/
private theorem DzKit.tp_val''',
    '''/-- The named tape `i` is the tape of index `i`. -/
private theorem DzKit.tp_val''')
rep('E7e', '''/-- The named tapes come first. -/''',
    '''/-- The diagonalizer has at least the fourteen named tapes: `14 ≤ κ.K`. -/''')
open(sys.argv[2], 'w', encoding='utf-8').write(src)
w = [(i, len(l)) for i, l in enumerate(src.split('\n'), 1) if len(l) > 100]
print('lines over 100 chars:', w)
assert not w
