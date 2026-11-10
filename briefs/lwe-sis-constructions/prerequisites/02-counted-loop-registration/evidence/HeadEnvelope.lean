import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.TuringMachine.Build.ModuleHost

set_option autoImplicit false

namespace LweSisGate14Preflight

open Complexity Turing Turing.ModuleHost

/-- The existing counted word loop can be installed as an H14 clean call
whose time budget also bounds each work head at every time. -/
theorem forLoop_clean_install_envelope {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) (B b : ℕ)
    (hbound : ∀ c d j, j ≤ c.length →
      (f^[j] d).length ≤ B * ((pairEncode c d).length + 1) ^ b) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      Clean M (BinArith.forLoop f) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
        ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
            (A * (arg.length + 1) ^ d : ℕ) := by
  obtain ⟨M, A, d, hclean⟩ :=
    clean_install (BinArith.polyTimeComputable_forLoop hf B b hbound)
  exact ⟨M, A, d, hclean, hclean.envelope⟩

#print axioms forLoop_clean_install_envelope
#print axioms Complexity.BinArith.forLoop_pairEncode
#print axioms Complexity.BinArith.polyTimeComputable_forLoop
#print axioms Complexity.BinArith.forLoop_bound_of_ctx
#print axioms Turing.ModuleHost.clean_install
#print axioms Turing.ModuleHost.Clean.envelope

end LweSisGate14Preflight
