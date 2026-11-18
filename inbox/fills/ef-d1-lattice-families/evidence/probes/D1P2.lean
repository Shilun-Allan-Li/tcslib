import TCSlib.Cryptography.LWE.Efficient
import TCSlib.Cryptography.SIS.Efficient
/-! D1-P2 consumer smoke test (evidence only): the assumptions stay on the raw families, and an
efficient family passes wherever a raw family is taken. -/
open TCSlib.Cryptography Complexity

example : ∀ (F : LWE.EfficientFamily) (_ : LWE.DLWEAssumption F.toFamily) (D : NUPPT),
    Negligible fun κ => F.toFamily.advantageAt D κ :=
  fun _ h D => h D
example : ∀ (F : SIS.EfficientFamily) (_ : SIS.SISAssumption F.toFamily) (D : NUPPT),
    Negligible fun κ => F.toFamily.successAt D κ :=
  fun _ h D => h D
-- a #377-style statement over `F : LWE.Family` accepts `F.toFamily`
def rawConsumer (F : LWE.Family) : Prop := LWE.DLWEAssumption F → True
example (F : LWE.EfficientFamily) : rawConsumer F.toFamily := fun _ => trivial
example (F : SIS.EfficientFamily) : (SIS.SISAssumption F.toFamily → True) := fun _ => trivial
-- the projections of the efficiency fields
example (F : LWE.EfficientFamily) := F.params_uniform
example (F : LWE.EfficientFamily) := F.noise_efficient
example (F : SIS.EfficientFamily) := F.params_uniform
#check LWE.dyadicExample.noise_efficient
