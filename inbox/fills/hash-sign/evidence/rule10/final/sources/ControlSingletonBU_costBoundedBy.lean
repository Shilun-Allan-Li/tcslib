import Lean
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative {ι α : Type} {spec : TCSlib.Cryptography.Games.OracleSpec ι} (a : α) (q : ℕ) : (TCSlib.Cryptography.Games.OracleComp.pure (spec := spec) a).CostBoundedBy (fun _ => 1) q := True.intro

theorem positive {ι α : Type} {spec : TCSlib.Cryptography.Games.OracleSpec ι} (a : α) (q : ℕ) : (TCSlib.Cryptography.Games.OracleComp.pure (spec := spec) a).CostBoundedBy (fun _ => 1) q := TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure (fun _ => 1) a q

end HashSignSensitivity

