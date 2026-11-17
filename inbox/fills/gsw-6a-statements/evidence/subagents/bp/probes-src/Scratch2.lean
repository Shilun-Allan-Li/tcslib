import TCSlib.Complexity.BranchingPrograms.Barrington
open BranchingProgram BoolCircuit Equiv
def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def nx1 : TreeCircuit 2 := .lit ⟨1, false⟩
def d1 : TreeCircuit 2 := .node true [x0, x1]
def d2 : TreeCircuit 2 := .node false [d1, .node true [x0, nx1]]
def timeIt (name : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{name}: {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  {t1 - t0} ms"
#eval timeIt "conj value" fun _ => toString ((List.finRange 5).map (conjugator sigma1 sigma2))
#eval timeIt "d1 len" fun _ => toString (barrington d1 sigma1).length
#eval timeIt "d1 yield" fun _ => toString ((List.finRange 5).map ((barrington d1 sigma1).yield fun _ => true))
#eval timeIt "d2 len" fun _ => toString (barrington d2 sigma1).length
#eval timeIt "d2 yield" fun _ => toString ((List.finRange 5).map ((barrington d2 sigma1).yield fun _ => true))
