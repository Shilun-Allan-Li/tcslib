import TCSlib.Complexity.BranchingPrograms.Barrington
open BranchingProgram BoolCircuit
def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/scratch/bl.progress" .append
  h.putStrLn s; h.flush
def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def andT : ℕ → TreeCircuit 2
  | 0 => x0
  | d + 1 => .node true [andT d, x1]
def orT : ℕ → TreeCircuit 2
  | 0 => x0
  | d + 1 => .node false [orT d, x1]
#eval show IO Unit from do
  for d in [1, 2, 3, 4, 5, 6] do
    let t0 ← IO.monoMsNow
    let B := barrington (andT d) sigma1
    let y := B.yield (fun _ => true) 0
    logp s!"and depth {d} len {B.length} yield {y} {(← IO.monoMsNow) - t0}ms"
  for d in [1, 2, 3, 4] do
    let t0 ← IO.monoMsNow
    let B := barrington (orT d) sigma1
    let y := B.yield (fun _ => true) 0
    logp s!"or depth {d} len {B.length} yield {y} {(← IO.monoMsNow) - t0}ms"
