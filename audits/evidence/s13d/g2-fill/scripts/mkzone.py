"""Write the G2 fill's prescribed overlay of `Build/Zone.lean` (read-only on its inputs).

Usage: python3 -I mkzone.py <base Zone.lean> <out overlay>

Content-anchored edits, each asserted to match exactly once:

  1. Two new privates before `Turing.zoneSide_cascadeRight`'s docstring: `zoneStepPair_pre` (the
     classical pre-state descends one level through the outer step pair; its proof is the block
     that `zoneSide_cascadeRight`'s successor case proves inline at the base), and
     `zoneCascadeRight_classical`, the one induction on the index giving both the two word
     equalities and the new home.
  2. `Turing.zoneSide_cascadeRight` is its first projection (statement byte-identical).
  3. `Turing.zoneCascadeRight_home`, the fill's target, is its second.
  4. The module status and the two sketches name the shared induction.

The pre-state argument and the induction skeleton are each written once (the first G2 screen of
the two separate inductions showed them reproducing each other at 52-54%).
"""
import sys

base, out = sys.argv[1:3]
t = open(base, encoding="utf-8").read()


def rep(a, b):
    global t
    c = t.count(a)
    assert c == 1, (a[:80], c)
    t = t.replace(a, b)


a = t.index("theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)")
b = t.index("theorem zoneCascadeRight_lengths", a)
region = t[a:b]
s0 = region.index("    have hroom' : (z.left ⟨j + 1, hj⟩).length + 2 ^ j ≤")
s1 = region.index("    have hinner := ih hjl (zoneStepPair (j + 1) z) hr' hl' hd' hroomlower\n")
block = region[s0:s1]
assert block.count("have ") == 8, block.count("have ")  # seven facts and the nested hp
body = "".join(l[2:] + "\n" if l.startswith("    ") else l + "\n" for l in block.rstrip("\n").split("\n"))
LEMMA = """/-- **The classical pre-state descends one level.** If `z` is in the classical pre-state of
`Turing.zoneSide_cascadeRight` at index `j + 1`, then the outer step pair `zoneStepPair (j + 1)`
leaves it in the classical pre-state at index `j`: the right zones below `j` empty, the left zones
below `j` full, a nonempty donor at `j`, and room for one pass on the left at `j`.

**Proof sketch.** The pair touches levels `j` and `j + 1` only (`zoneStepPair_frame`), so the
levels below `j` keep their empty right and full left words. At level `j` it moves the donor's
first `2^j` cells in, which are nonempty since the donor is, and leaves `2^j` cells on the left,
which with `2^(j-1)` more fit the capacity `2 · 2^j` (`zoneStepPair_active`). -/
private theorem zoneStepPair_pre {ℓ : ℕ} (j : ℕ) (hj : j + 1 < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j + 1), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j + 1), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j + 1, hj⟩ ≠ [])
    (hroom : (z.left ⟨j + 1, hj⟩).length + 2 ^ (j + 1 - 1) ≤ zoneCapacity (j + 1)) :
    (∀ k (hk : k < j), (zoneStepPair (j + 1) z).right ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j),
      ((zoneStepPair (j + 1) z).left ⟨k, by omega⟩).length = zoneCapacity k) ∧
    (zoneStepPair (j + 1) z).right ⟨j, by omega⟩ ≠ [] ∧
    ((zoneStepPair (j + 1) z).left ⟨j, by omega⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j := by
  have hjl : j < ℓ := by omega
""" + body + """  exact ⟨hr', hl', hd', hroomlower⟩

/-- **The classical right cascade, both facts by one induction.** Under the classical pre-state
at index `j`, the cascade's words are the old ones with the home pushed on the left and the right
word's head popped (`Turing.zoneSide_cascadeRight`), and its new home is that head
(`Turing.zoneCascadeRight_home`).

**Proof sketch.** Induction on `j`. At `0` the cascade is the central move: it pushes the old home
on the left and pops the donor's head into the home (`Turing.zoneSide_moveRight`), and the donor,
zone `0`, is the right word's first word. At `j + 1` the outer step pair leaves the pre-state at
`j` (`zoneStepPair_pre`), and both step pairs keep both concatenations and the home
(`zoneStepPair_side`), so the induction hypothesis gives both facts. -/
private theorem zoneCascadeRight_classical {ℓ : ℕ} (j : ℕ) (hj : j < ℓ) (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ [])
    (hroom : (z.left ⟨j, hj⟩).length + 2 ^ (j - 1) ≤ zoneCapacity j) :
    (zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
      zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail) ∧
    (zoneCascadeRight j z).home = (zoneSide z.right).headI := by
  induction j generalizing z with
  | zero =>
    have hroom0 : (z.left ⟨0, hj⟩).length + 1 ≤ zoneCapacity 0 := by
      simpa using hroom
    simp only [zoneCascadeRight, List.range_zero, List.reverse_nil,
      List.foldl_nil, zoneMove, dif_pos hj, dif_pos hroom0]
    refine ⟨zoneSide_moveRight hj z hroom0 hdonor, ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨a, as, ha⟩ := List.exists_cons_of_ne_nil hdonor
    simp only [zoneMoveRight]
    rw [zoneSide_succ, show (0 : Fin (n + 1)) = ⟨0, hj⟩ from rfl, ha]
    rfl
  | succ j ih =>
    obtain ⟨hr', hl', hd', hroomlower⟩ := zoneStepPair_pre j hj z hr hl hdonor hroom
    obtain ⟨hinner, hhome⟩ := ih (by omega) (zoneStepPair (j + 1) z) hr' hl' hd' hroomlower
    rw [zoneCascadeRight_succ]
    refine ⟨?_, ?_⟩
    · rw [(zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2, hinner.1, hinner.2,
        (zoneStepPair_side _ _).1, (zoneStepPair_side _ _).2]
      exact ⟨rfl, rfl⟩
    · show (zoneCascadeRight j (zoneStepPair (j + 1) z)).home = _
      rw [hhome, (zoneStepPair_side _ _).2]

"""
DOC = "/-- The cascade realizes exactly one virtual right move. Preconditions are\n"
rep(DOC, LEMMA + DOC)
p0 = region.index("    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail := by\n  induction j")
p1 = region.index("    exact ⟨rfl, rfl⟩\n") + len("    exact ⟨rfl, rfl⟩\n")
assert region[p1:].startswith("\n/-- The cascade restores the half-full discipline")
new_region = region[:p0] + \
    "    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail :=\n" + \
    "  (zoneCascadeRight_classical j hj z hr hl hdonor hroom).1\n" + region[p1:]
rep(region, new_region)
# 3. the target is the shared induction's second projection (the maintainer's G2 fill,
#    user 2026-10-15)
TGT = """    (zoneCascadeRight j z).home = (zoneSide z.right).headI := by
  sorry
"""
rep(TGT, """    (zoneCascadeRight j z).home = (zoneSide z.right).headI :=
  (zoneCascadeRight_classical j hj z hr hl hdonor hroom).2
""")
# 4. the module status and the target's sketch (the proof is an induction on the index)
rep("""**Status: proved, apart from one cascade fact.** Every declaration is proved except
`Turing.zoneCascadeRight_home` (the cascade's new home is the right word's first cell), sorried
under its proof sketch for the G4 fill. History: the statement phase of tranche A-S2""", """**Status: proved.** Every declaration is proved; the last, `Turing.zoneCascadeRight_home` (the
cascade's new home is the right word's first cell), in the §13d G2 fill. History: the
statement phase of tranche A-S2""")
rep("""leaves zone `0` nonempty (each descending prefix of the nonempty donor is nonempty, as in the
proof of `Turing.zoneSide_cascadeRight`), and zone `0` is the first word of the
concatenation, so its head is the right word's head. -/""", """leaves zone `0` nonempty (each descending prefix of the nonempty donor is nonempty, as in the
proof of `Turing.zoneSide_cascadeRight`), and zone `0` is the first word of the
concatenation, so its head is the right word's head. Formally the induction on `j` is shared
with `Turing.zoneSide_cascadeRight` (the private `zoneCascadeRight_classical`): at `0` the
cascade is the central move, which sets the home to the donor's head; at `j + 1` the outer step
pair keeps the right concatenation and leaves the pre-state at `j`. -/""")
rep("""(`zoneSide_moveRight`) gives exactly the two word equalities. Half-full
restoration is **not** used. -/""", """(`zoneSide_moveRight`) gives exactly the two word equalities. Half-full
restoration is **not** used. Formally the induction on `j` is shared with
`Turing.zoneCascadeRight_home` (the private `zoneCascadeRight_classical`). -/""")
open(out, "w", encoding="utf-8").write(t)
print(f"zone overlay written: {len(t.splitlines())} lines; 2 private lemmas added, "
      f"1 proof made a projection, the target proved as the other")
