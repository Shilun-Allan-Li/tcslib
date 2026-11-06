# Apply the review's landing edits E1-E6 to a worktree: apply_edits.py <worktree>
import sys,os
R=sys.argv[1]; D=os.path.join(R,'TCSlib/Cryptography/ZeroKnowledge/ThreeColoring')
def rep(path,old,new):
    s=open(path).read()
    assert s.count(old)==1, (path, old[:60], s.count(old))
    open(path,'w').write(s.replace(old,new))
# E1 facade
f=D+'.lean'
rep(f,"import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol\n",
 "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol\n"
 "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas\n"
 "import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKMachine\n")
rep(f,"  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]\n  (Prop-127.6).\n",
 "  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]\n  (Prop-127.6).\n"
 "* `ColZKLemmas` — generic lemmas of the `col_zk` ladder: disjoint fields of a uniform tape are\n"
 "  independent and uniform, averaging over seeds, first-success searches split at an index, and\n"
 "  the negligibility of the error of [PS10, Proposition 128.8].\n"
 "* `ColZKMachine` — the hiding reduction of [PS10, proof of Proposition 128.8] with its attempt\n"
 "  table fixed, as a machine (`hidingView`, `exists_colHidingRed`), the two-parameter coin\n"
 "  transport and the hiding bound for all the fixed reductions at once.\n")
# E2 stale name in ColZKLemmas module docstring
f=D+'/ColZKLemmas.lean'
rep(f,"function (`negligible_colZKErr`, `colZK_attempts_le`).","function (`negligible_colZKErr`).")
# E3 findSome?_map_option: cite core List.map_findSome?
rep(f,"""/-- Mapping the values of a search: `l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g`. -/
theorem findSome?_map_option {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases f a with
    | none => exact ih
    | some b => rfl
""","""/-- Mapping the values of a search: `l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g`
(core `List.map_findSome?`, read from right to left, with the composite written pointwise). -/
theorem findSome?_map_option {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g :=
  List.map_findSome?.symm
""")
# E4 acceptProb_seed_to_coins is acceptProb_bind reversed: delete it, cite acceptProb_bind
rep(f,"""/-- **Moving a seed factor into the distinguisher's coins**, for one sampler
(`acceptProb_def`, `Equiv.prodAssoc`). -/
theorem acceptProb_seed_to_coins {σ κ γ γ' ρ : Type*} [Fintype σ] [Fintype κ] [Fintype ρ]
    (X : σ → γ) (F : γ → κ → γ') (D : γ' → ρ → Bool) :
    acceptProb (fun s : σ × κ => F (X s.1) s.2) D =
      acceptProb X fun g (c : κ × ρ) => D (F g c.1) c.2 := by
  rw [acceptProb_def, acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc σ κ ρ).symm]
  rfl

""","")
rep(f,"""`κ × ρ` (`acceptProb_seed_to_coins`). -/""","""`κ × ρ` (`acceptProb_bind` on both samplers). -/""")
rep(f,"""  rw [distAdv_def, distAdv_def, acceptProb_seed_to_coins, acceptProb_seed_to_coins]""",
 """  rw [distAdv_def, distAdv_def, acceptProb_bind, acceptProb_bind]""")
# E5 layout: blank lines between declarations, triple blank line
f=D+'/Simulator.lean'
rep(f,"  rw [h1, h2]\n/-- **The real view","  rw [h1, h2]\n\n/-- **The real view")
rep(f,"      ColMachines.edgeAt_eq_some_of_pos G hm]\n/-- **`colSim` is","      ColMachines.edgeAt_eq_some_of_pos G hm]\n\n/-- **`colSim` is")
rep(f,"    _ ≤ _ := by linarith [hexp]\n\n\n\n/-- **`col_zk` from","    _ ≤ _ := by linarith [hexp]\n\n/-- **`col_zk` from")
# E6 the source tag of colSimRed_fixed_eq
rep(f,"/-- **With the attempt table fixed only attempt `k` reads the challenge** (Claim-129.d): the",
 "/-- **With the attempt table fixed only attempt `k` reads the challenge** [PS10, proof of\nProposition 128.8, the reduction to the hiding property] (Claim-129.d): the")
print('ok')
