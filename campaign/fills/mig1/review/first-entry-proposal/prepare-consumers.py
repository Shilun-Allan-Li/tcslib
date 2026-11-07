"""Archive small hypothetical consumers and effective paired definition controls."""
from pathlib import Path
OUT=Path(__file__).resolve().parent
SEAL='attribute [local irreducible] Turing.MultiTapeTM.runFrom Turing.MultiTapeTM.step\n'
proposal=(OUT/'Proposed-contract.lean.txt').read_text()
consumer='''import TCSlib.Complexity.TuringMachine.Build.Primitives
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Turing

'''+SEAL+'''
namespace Turing.MultiTapeTM
'''+proposal+'''
end Turing.MultiTapeTM

namespace FirstEntryProposal

theorem loop_private_shape {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  exact tm.exists_first_entry_of_fixed stop c d T hfix hd hT

theorem primitives_private_shape {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  exact tm.exists_first_entry_of_fixed stop c d T hfix hd hT

theorem singleton_stop_shape {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧
      tm.runFrom c t = d := by
  obtain ⟨t, ht, hfirst, he⟩ :=
    tm.exists_first_entry_of_fixed (fun r => r = q) c d T
      (by
        intro z hz
        rcases hz with ⟨r, hs, rfl⟩
        exact hfix z hs) ⟨q, hd, rfl⟩ hT
  exact ⟨t, ht, fun j hj hs => hfirst j hj ⟨q, hs, rfl⟩, he⟩

theorem comparator_stop_shape {k : ℕ} {w : List Bool}
    (tm : MultiTapeTM k Bool (Fin 3 × Bool))
    (c d : Cfg k Bool (Fin 3 × Bool) w) (T : ℕ) (b : Bool)
    (hfix : ∀ z : Cfg k Bool (Fin 3 × Bool) w,
      (∃ b', z.state = some ((2 : Fin 3), b')) → tm.step z = z)
    (hd : d.state = some ((2 : Fin 3), b)) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ∀ b', (tm.runFrom c j).state ≠ some ((2 : Fin 3), b')) ∧
      tm.runFrom c t = d := by
  obtain ⟨t, ht, hfirst, he⟩ :=
    tm.exists_first_entry_of_fixed (fun q => q.1 = (2 : Fin 3)) c d T
      (by
        intro z hz
        rcases hz with ⟨⟨i, b'⟩, hs, hi⟩
        change i = (2 : Fin 3) at hi
        subst i
        exact hfix z ⟨b', hs⟩) ⟨((2 : Fin 3), b), hd, rfl⟩ hT
  exact ⟨t, ht, fun j hj b' hs => hfirst j hj ⟨((2 : Fin 3), b'), hs, rfl⟩, he⟩

end FirstEntryProposal

#print axioms Turing.MultiTapeTM.exists_first_entry_of_fixed
#print axioms FirstEntryProposal.loop_private_shape
#print axioms FirstEntryProposal.primitives_private_shape
#print axioms FirstEntryProposal.singleton_stop_shape
#print axioms FirstEntryProposal.comparator_stop_shape
'''
controls='''import TCSlib.Complexity.TuringMachine.Finite
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Turing

-- Step: halting delta, pointwise and abstracted.
example (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) :
    tm.step {c with state := none} = {c with state := none} := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) =>
    tm.step {c with state := none}) = fun _ c => {c with state := none} := by rfl

-- Step: complete defining equation, pointwise and abstracted.
example (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) :
    tm.step c = (match c.state with
      | none => c
      | some q => (tm.tr q c.inputSymbol c.workTapeSymbols).apply c) := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) =>
    tm.step c) = fun tm c => (match c.state with
      | none => c
      | some q => (tm.tr q c.inputSymbol c.workTapeSymbols).apply c) := by rfl

-- Run: zero-time delta, pointwise and abstracted.
example (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) :
    tm.runFrom c 0 = c := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) =>
    tm.runFrom c 0) = fun _ c => c := by rfl

-- Run: complete defining equation, pointwise and abstracted.
example (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool)) (n : ℕ) :
    tm.runFrom c n = (tm.step)^[n] c := by rfl
example : (fun (tm : MultiTapeTM 1 Bool Unit) (c : Cfg 1 Bool Unit ([] : List Bool))
    (n : ℕ) => tm.runFrom c n) = fun tm c n => (tm.step)^[n] c := by rfl
'''
for name,text in [('Consumers-v1.lean.txt',consumer),
                  ('Controls-unsealed.lean.txt',controls),
                  ('Controls-sealed.lean.txt',controls.replace('open Turing\n','open Turing\n'+SEAL,1))]:
    p=OUT/name
    assert not p.exists(),p
    p.write_text(text)
print('Prepared four sealed consumer shapes and eight paired controls.')
