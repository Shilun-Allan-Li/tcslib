"""Insert the zone-layer specification API into Build/Zone.lean and Build/ZoneTape.lean.
Every insertion is anchored on text that must occur exactly once; the script asserts it."""
import sys
root = sys.argv[1]
TAG = "(the specification API, user 2026-10-16)"
SIMPS = "attribute [simps (config := { isSimp := false }) home left right]"

def edit(path, pairs):
    p = f"{root}/{path}"
    s = open(p).read()
    for anchor, new in pairs:
        n = s.count(anchor)
        assert n == 1, (path, anchor[:60], n)
        s = s.replace(anchor, new)
    open(p, "w").write(s)

Z = "TCSlib/Complexity/TuringMachine/Build/Zone.lean"
T = "TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean"

edit(Z, [
# zoneCapacity_eq: state the formula (bare-label docstring repaired)
("/-- **A zone's capacity as an equation** (the specification API, user 2026-10-16). -/\n",
 f"/-- Zone `i` holds `2 · 2^i` virtual cells per side: `zoneCapacity i = 2 * 2 ^ i` {TAG}. -/\n"),
# zoneBase
("def zoneBase (i : ℕ) : ℕ := 2 * (2 ^ i - 1)\n",
 "def zoneBase (i : ℕ) : ℕ := 2 * (2 ^ i - 1)\n\n"
 f"/-- Zone `i`'s first virtual slot is `2 · (2^i - 1)`: `zoneBase i = 2 * (2 ^ i - 1)`\n{TAG}. -/\n"
 "theorem zoneBase_eq (i : ℕ) : zoneBase i = 2 * (2 ^ i - 1) :=\n  rfl\n"),
# zoneIndex
("def zoneIndex (s : ℕ) : ℕ := Nat.log2 (s / 2 + 1)\n",
 "def zoneIndex (s : ℕ) : ℕ := Nat.log2 (s / 2 + 1)\n\n"
 f"/-- Slot `s` lies in zone `log₂ (⌊s / 2⌋ + 1)`: `zoneIndex s = Nat.log2 (s / 2 + 1)`\n{TAG}. -/\n"
 "theorem zoneIndex_eq (s : ℕ) : zoneIndex s = Nat.log2 (s / 2 + 1) :=\n  rfl\n"),
# zoneSlot
("""  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none
""",
 """  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none

/-- A slot of a laid-out zone reads that zone's word at the slot's offset from the zone's base:
`zoneSlot w s = (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?` when `zoneIndex s < ℓ`
""" + TAG + """. -/
theorem zoneSlot_of_lt {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) {s : ℕ} (h : zoneIndex s < ℓ) :
    zoneSlot w s = (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]? := by
  simp only [zoneSlot, dif_pos h]

/-- A slot beyond the laid-out zones is unoccupied: `zoneSlot w s = none` when
`ℓ ≤ zoneIndex s` """ + TAG + """. -/
theorem zoneSlot_of_le {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) {s : ℕ} (h : ℓ ≤ zoneIndex s) :
    zoneSlot w s = none := by
  simp only [zoneSlot, dif_neg (show ¬ zoneIndex s < ℓ by omega)]
"""),
# ZoneContents.empty
("""  left_le := fun _ => by simp
  right_le := fun _ => by simp
""",
 """  left_le := fun _ => by simp
  right_le := fun _ => by simp

""" + SIMPS + """ ZoneContents.empty
"""),
# zoneSide
("""def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i
""",
 """def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

/-- A side's half-word is its zone words concatenated in level order:
`zoneSide w = (List.finRange ℓ).flatMap w` """ + TAG + """. -/
theorem zoneSide_eq {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) :
    zoneSide w = (List.finRange ℓ).flatMap fun i => w i :=
  rfl
"""),
# zoneShiftInW
("""      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j
""",
 """      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j

/-- The inward shift's word at level `j`: when `1 ≤ i < ℓ` and zone `i - 1` is empty, level
`i - 1` gets the first `2^(i-1)` cells of zone `i`, level `i` keeps the rest, and every other
level, like every level outside the guard, is unchanged """ + TAG + """. -/
theorem zoneShiftInW_eq {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) (j : Fin ℓ) :
    zoneShiftInW i w j =
      if hi : 1 ≤ i ∧ i < ℓ then
        if w ⟨i - 1, by omega⟩ = [] then
          if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
          else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
          else w j
        else w j
      else w j :=
  rfl
"""),
# zoneShiftOutW
("""      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j
""",
 """      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j

/-- The outward shift's word at level `j`: when `1 ≤ i < ℓ`, zone `i - 1` is full and zone `i`
has room for `2^(i-1)` more cells, level `i - 1` keeps its first `2^(i-1)` cells, level `i`
gets the rest of them in front of its word, and every other level, like every level outside the
guard, is unchanged """ + TAG + """. -/
theorem zoneShiftOutW_eq {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) (j : Fin ℓ) :
    zoneShiftOutW i w j =
      if hi : 1 ≤ i ∧ i < ℓ then
        if (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
            (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i then
          if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
          else if j.val = i then
            (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
          else w j
        else w j
      else w j :=
  rfl
"""),
# zoneShiftIn
("""    cases side
    · exact z.right_le
    · exact zoneShiftInW_capacity i z.right z.right_le
""",
 """    cases side
    · exact z.right_le
    · exact zoneShiftInW_capacity i z.right z.right_le

""" + SIMPS + """ zoneShiftIn
"""),
# zoneShiftOut
("""    cases side
    · exact z.right_le
    · exact zoneShiftOutW_capacity i z.right z.right_le
""",
 """    cases side
    · exact z.right_le
    · exact zoneShiftOutW_capacity i z.right z.right_le

""" + SIMPS + """ zoneShiftOut
"""),
# zoneHomeWrite
("""    ZoneContents ℓ := { z with home := v }
""",
 """    ZoneContents ℓ := { z with home := v }

""" + SIMPS + """ zoneHomeWrite
"""),
# zoneMoveRight / zoneMoveLeft: anchor on the unique endings
("""    · simpa only [List.length_tail] using
        (Nat.sub_le (z.right j).length 1).trans (z.right_le j)
    · exact z.right_le j

/-- The mirrored left step. -/
""",
 """    · simpa only [List.length_tail] using
        (Nat.sub_le (z.right j).length 1).trans (z.right_le j)
    · exact z.right_le j

""" + SIMPS + """ zoneMoveRight

/-- The mirrored left step. -/
"""),
("""      simpa only [List.length_cons] using hroom
    · exact z.right_le j

/-- The totally guarded head step""",
 """      simpa only [List.length_cons] using hroom
    · exact z.right_le j

""" + SIMPS + """ zoneMoveLeft

/-- The totally guarded head step"""),
# zoneMove
("""    | false =>
      if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveLeft hℓ z h
      else z
  else z
""",
 """    | false =>
      if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveLeft hℓ z h
      else z
  else z

/-- The guarded right step is `Turing.zoneMoveRight` when `0 < ℓ` and the left zone `0` has room
for one more cell, and the identity otherwise """ + TAG + """. -/
theorem zoneMove_true {ℓ : ℕ} (z : ZoneContents ℓ) :
    zoneMove true z =
      if hℓ : 0 < ℓ then
        if h : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then zoneMoveRight hℓ z h else z
      else z :=
  rfl

/-- The guarded left step is `Turing.zoneMoveLeft` when `0 < ℓ` and the right zone `0` has room
for one more cell, and the identity otherwise """ + TAG + """. -/
theorem zoneMove_false {ℓ : ℕ} (z : ZoneContents ℓ) :
    zoneMove false z =
      if hℓ : 0 < ℓ then
        if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then zoneMoveLeft hℓ z h else z
      else z :=
  rfl
"""),
# zoneStepPair, zoneCascadeRight
("""def zoneStepPair {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  zoneShiftOut false i (zoneShiftIn true i z)
""",
 """def zoneStepPair {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  zoneShiftOut false i (zoneShiftIn true i z)

/-- A cascade stage is the right inward shift followed by the left outward shift:
`zoneStepPair i z = zoneShiftOut false i (zoneShiftIn true i z)` """ + TAG + """. -/
theorem zoneStepPair_eq {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) :
    zoneStepPair i z = zoneShiftOut false i (zoneShiftIn true i z) :=
  rfl
"""),
("""  (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
    (zoneMove true
      ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z))
""",
 """  (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
    (zoneMove true
      ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z))

/-- The right cascade at index `j` runs the stages at levels `j, …, 1`, the guarded right step,
then the stages at levels `1, …, j` """ + TAG + """. -/
theorem zoneCascadeRight_eq {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeRight j z =
      (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
        (zoneMove true
          ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z)) :=
  rfl
"""),
# words
("""def ZoneContents.words {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) : Fin ℓ → List (Option Bool) :=
  if side then z.right else z.left
""",
 """def ZoneContents.words {ℓ : ℕ} (side : Bool) (z : ZoneContents ℓ) : Fin ℓ → List (Option Bool) :=
  if side then z.right else z.left

/-- The right side's words are the right stack: `z.words true = z.right` """ + TAG + """. -/
theorem ZoneContents.words_true {ℓ : ℕ} (z : ZoneContents ℓ) : z.words true = z.right :=
  rfl

/-- The left side's words are the left stack: `z.words false = z.left` """ + TAG + """. -/
theorem ZoneContents.words_false {ℓ : ℕ} (z : ZoneContents ℓ) : z.words false = z.left :=
  rfl
"""),
# swap
("""  left := z.right
  right := z.left
  left_le := z.right_le
  right_le := z.left_le
""",
 """  left := z.right
  right := z.left
  left_le := z.right_le
  right_le := z.left_le

""" + SIMPS + """ ZoneContents.swap
"""),
# zoneCascadeLeft, zoneCascade
("""def zoneCascadeLeft {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (zoneCascadeRight j z.swap).swap
""",
 """def zoneCascadeLeft {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (zoneCascadeRight j z.swap).swap

/-- The left cascade is the mirrored right cascade:
`zoneCascadeLeft j z = (zoneCascadeRight j z.swap).swap` """ + TAG + """. -/
theorem zoneCascadeLeft_eq {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascadeLeft j z = (zoneCascadeRight j z.swap).swap :=
  rfl
"""),
("""def zoneCascade {ℓ : ℕ} (dir : Bool) (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if dir then zoneCascadeRight j z else zoneCascadeLeft j z
""",
 """def zoneCascade {ℓ : ℕ} (dir : Bool) (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if dir then zoneCascadeRight j z else zoneCascadeLeft j z

/-- The cascade for a right move is the right cascade:
`zoneCascade true j z = zoneCascadeRight j z` """ + TAG + """. -/
theorem zoneCascade_true {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascade true j z = zoneCascadeRight j z :=
  rfl

/-- The cascade for a left move is the left cascade:
`zoneCascade false j z = zoneCascadeLeft j z` """ + TAG + """. -/
theorem zoneCascade_false {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) :
    zoneCascade false j z = zoneCascadeLeft j z :=
  rfl
"""),
# zoneShiftIndex
("""def zoneShiftIndex {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ℕ :=
  (List.finRange ℓ).findIdx fun i => !(z.words dir i).isEmpty
""",
 """def zoneShiftIndex {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ℕ :=
  (List.finRange ℓ).findIdx fun i => !(z.words dir i).isEmpty

/-- The scanned index is the position of the first level whose feeding-side word is nonempty:
`zoneShiftIndex dir z = (List.finRange ℓ).findIdx (fun i => !(z.words dir i).isEmpty)`
""" + TAG + """. -/
theorem zoneShiftIndex_eq_findIdx {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) :
    zoneShiftIndex dir z = (List.finRange ℓ).findIdx fun i => !(z.words dir i).isEmpty :=
  rfl
"""),
# zoneRebalance_of_lt, after zoneRebalance_of_le
("""    (h : ℓ ≤ zoneShiftIndex dir z) : zoneRebalance dir z = z := by
  simp [zoneRebalance, show ¬ zoneShiftIndex dir z < ℓ by omega]
""",
 """    (h : ℓ ≤ zoneShiftIndex dir z) : zoneRebalance dir z = z := by
  simp [zoneRebalance, show ¬ zoneShiftIndex dir z < ℓ by omega]

/-- With a nonempty feeding zone the rebalance is the cascade at the scanned index:
`zoneRebalance dir z = zoneCascade dir (zoneShiftIndex dir z) z` when
`zoneShiftIndex dir z < ℓ` """ + TAG + """. -/
theorem zoneRebalance_of_lt {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ)
    (h : zoneShiftIndex dir z < ℓ) :
    zoneRebalance dir z = zoneCascade dir (zoneShiftIndex dir z) z := by
  simp only [zoneRebalance, if_pos h]
"""),
# extend
("""    · simp only [Fin.lastCases_last, List.length_replicate, Fin.val_last, zoneCapacity]
      omega
    · simpa only [Fin.lastCases_castSucc, Fin.coe_castSucc] using z.right_le j
""",
 """    · simp only [Fin.lastCases_last, List.length_replicate, Fin.val_last, zoneCapacity]
      omega
    · simpa only [Fin.lastCases_castSucc, Fin.coe_castSucc] using z.right_le j

""" + SIMPS + """ ZoneContents.extend
"""),
# zoneTrackTape
("""  if p = 0 then z.home
  else if 0 < p then ((zoneSide z.right)[(p - 1).toNat]?).join
  else ((zoneSide z.left)[(-p - 1).toNat]?).join
""",
 """  if p = 0 then z.home
  else if 0 < p then ((zoneSide z.right)[(p - 1).toNat]?).join
  else ((zoneSide z.left)[(-p - 1).toNat]?).join

/-- The represented tape reads the home at the head: `zoneTrackTape z 0 = z.home` """ + TAG + """. -/
theorem zoneTrackTape_zero {ℓ : ℕ} (z : ZoneContents ℓ) : zoneTrackTape z 0 = z.home := by
  unfold zoneTrackTape
  exact if_pos rfl

/-- At a positive position `p` the represented tape reads cell `p - 1` of the right half-word, a
stored blank and a position beyond it both reading blank:
`zoneTrackTape z p = ((zoneSide z.right)[(p - 1).toNat]?).join` """ + TAG + """. -/
theorem zoneTrackTape_of_pos {ℓ : ℕ} (z : ZoneContents ℓ) {p : ℤ} (hp : 0 < p) :
    zoneTrackTape z p = ((zoneSide z.right)[(p - 1).toNat]?).join := by
  simp only [zoneTrackTape, if_neg (show p ≠ 0 by omega), if_pos hp]

/-- At a negative position `p` the represented tape reads cell `-p - 1` of the left half-word, a
stored blank and a position beyond it both reading blank:
`zoneTrackTape z p = ((zoneSide z.left)[(-p - 1).toNat]?).join` """ + TAG + """. -/
theorem zoneTrackTape_of_neg {ℓ : ℕ} (z : ZoneContents ℓ) {p : ℤ} (hp : p < 0) :
    zoneTrackTape z p = ((zoneSide z.left)[(-p - 1).toNat]?).join := by
  simp only [zoneTrackTape, if_neg (show p ≠ 0 by omega), if_neg (show ¬ 0 < p by omega)]
"""),
])

edit(T, [
# zoneSlotOf
("""def zoneSlotOf {k : ℕ} (t : Fin k) : ZoneSym k → Option (Option Bool)
  | .inl _ => none
  | .inr c => c t
""",
 """def zoneSlotOf {k : ℕ} (t : Fin k) : ZoneSym k → Option (Option Bool)
  | .inl _ => none
  | .inr c => c t

/-- A binary symbol has `⊠` in every track's slot: `zoneSlotOf t (.inl b) = none`
""" + TAG + """. -/
theorem zoneSlotOf_inl {k : ℕ} (t : Fin k) (b : Bool) : zoneSlotOf t (.inl b) = none :=
  rfl

/-- A zone cell's track-`t` slot is its `t`-th entry: `zoneSlotOf t (.inr c) = c t`
""" + TAG + """. -/
theorem zoneSlotOf_inr {k : ℕ} (t : Fin k) (c : ZoneCell k) : zoneSlotOf t (.inr c) = c t :=
  rfl
"""),
# zoneCellOfCell
("""def zoneCellOfCell {k : ℕ} : Option (ZoneSym k) → ZoneCell k
  | some (.inr c) => c
  | _ => fun _ => none
""",
 """def zoneCellOfCell {k : ℕ} : Option (ZoneSym k) → ZoneCell k
  | some (.inr c) => c
  | _ => fun _ => none

/-- A physical cell holding a zone cell gives that cell: `zoneCellOfCell (some (.inr c)) = c`
""" + TAG + """. -/
theorem zoneCellOfCell_inr {k : ℕ} (c : ZoneCell k) : zoneCellOfCell (some (.inr c)) = c :=
  rfl

/-- A physical cell holding a binary symbol gives the all-`⊠` cell:
`zoneCellOfCell (some (.inl b)) = fun _ => none` """ + TAG + """. -/
theorem zoneCellOfCell_inl {k : ℕ} (b : Bool) :
    zoneCellOfCell (k := k) (some (.inl b)) = fun _ => none :=
  rfl

/-- A blank physical cell gives the all-`⊠` cell: `zoneCellOfCell none = fun _ => none`
""" + TAG + """. -/
theorem zoneCellOfCell_none {k : ℕ} : zoneCellOfCell (k := k) none = fun _ => none :=
  rfl
"""),
# zoneSlotSet
("""    ZoneSym k :=
  .inr (Function.update (zoneCellOfCell cell) t s)
""",
 """    ZoneSym k :=
  .inr (Function.update (zoneCellOfCell cell) t s)

/-- Setting track `t`'s slot to `s` gives the zone cell of the old cell updated at `t`:
`zoneSlotSet t cell s = .inr (Function.update (zoneCellOfCell cell) t s)` """ + TAG + """. -/
theorem zoneSlotSet_eq {k : ℕ} (t : Fin k) (cell : Option (ZoneSym k)) (s : Option (Option Bool)) :
    zoneSlotSet t cell s = .inr (Function.update (zoneCellOfCell cell) t s) :=
  rfl
"""),
# zoneOwner
("""def zoneOwner (ℓ n : ℕ) : Option (Fin ℓ) :=
  Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i
""",
 """def zoneOwner (ℓ n : ℕ) : Option (Fin ℓ) :=
  Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i

/-- The owner of distance `n` is the first laid-out zone whose cells contain `n`:
`zoneOwner ℓ n = Fin.find (fun i => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i)`
""" + TAG + """. -/
theorem zoneOwner_eq (ℓ n : ℕ) :
    zoneOwner ℓ n = Fin.find fun i : Fin ℓ => zoneStart i ≤ n ∧ n < zoneStart i + zoneCapacity i :=
  rfl
"""),
# zoneCells
("""    List (ZoneSym k) :=
  (List.range (zoneCapacity i)).map fun p => .inr fun t => ((z t).words side i)[p]?
""",
 """    List (ZoneSym k) :=
  (List.range (zoneCapacity i)).map fun p => .inr fun t => ((z t).words side i)[p]?

/-- Zone `i`'s cells are its `zoneCapacity i` offsets, offset `p` holding in track `t`'s slot
cell `p` of that track's zone word, or `⊠` beyond it:
`zoneCells side z i = (List.range (zoneCapacity i)).map (fun p => .inr fun t => …[p]?)`
""" + TAG + """. -/
theorem zoneCells_eq {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (i : Fin ℓ) :
    zoneCells side z i =
      (List.range (zoneCapacity i)).map fun p => .inr fun t => ((z t).words side i)[p]? :=
  rfl
"""),
# zoneCellAt
("""    Option (ZoneSym k) :=
  (zoneOwner ℓ n).map fun i => .inr fun t => ((z t).words side i)[n - zoneStart i]?
""",
 """    Option (ZoneSym k) :=
  (zoneOwner ℓ n).map fun i => .inr fun t => ((z t).words side i)[n - zoneStart i]?

/-- The cell at distance `n` is, for its owner `i`, the zone cell holding in track `t`'s slot
cell `n - zoneStart i` of that track's zone word, and blank without an owner:
`zoneCellAt side z n = (zoneOwner ℓ n).map (fun i => .inr fun t => …[n - zoneStart i]?)`
""" + TAG + """. -/
theorem zoneCellAt_eq {k ℓ : ℕ} (side : Bool) (z : Fin k → ZoneContents ℓ) (n : ℕ) :
    zoneCellAt side z n =
      (zoneOwner ℓ n).map fun i => .inr fun t => ((z t).words side i)[n - zoneStart i]? :=
  rfl
"""),
# zonedTape
("""  if c = 0 then some (.inr fun t => some (z t).home)
  else if 0 < c then zoneCellAt true z c.toNat
  else zoneCellAt false z (-c).toNat
""",
 """  if c = 0 then some (.inr fun t => some (z t).home)
  else if 0 < c then zoneCellAt true z c.toNat
  else zoneCellAt false z (-c).toNat

/-- A positive cell of the zoned tape is the right side's cell at that distance:
`zonedTape z c = zoneCellAt true z c.toNat` when `0 < c` """ + TAG + """. -/
theorem zonedTape_of_pos {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) {c : ℤ} (hc : 0 < c) :
    zonedTape z c = zoneCellAt true z c.toNat := by
  simp only [zonedTape, if_neg (show c ≠ 0 by omega), if_pos hc]

/-- A negative cell of the zoned tape is the left side's cell at that distance:
`zonedTape z c = zoneCellAt false z (-c).toNat` when `c < 0` """ + TAG + """. -/
theorem zonedTape_of_neg {k ℓ : ℕ} (z : Fin k → ZoneContents ℓ) {c : ℤ} (hc : c < 0) :
    zonedTape z c = zoneCellAt false z (-c).toNat := by
  simp only [zonedTape, if_neg (show c ≠ 0 by omega), if_neg (show ¬ 0 < c by omega)]
"""),
])
print("ok")
