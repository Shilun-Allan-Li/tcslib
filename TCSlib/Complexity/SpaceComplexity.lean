/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Machines.Layout
import TCSlib.Complexity.SpaceComplexity.Machines.Program
import TCSlib.Complexity.SpaceComplexity.Machines.Sim
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn
import TCSlib.Complexity.SpaceComplexity.Machines.Call
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec
import TCSlib.Complexity.SpaceComplexity.Machines.Frag
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain
import TCSlib.Complexity.SpaceComplexity.Machines.Parse
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp
import TCSlib.Complexity.SpaceComplexity.Machines.ARM
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace
import TCSlib.Complexity.SpaceComplexity.CounterProgSim
import TCSlib.Complexity.SpaceComplexity.CounterProgSimRun
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Inclusions
import TCSlib.Complexity.SpaceComplexity.Examples
import TCSlib.Complexity.SpaceComplexity.ZeroSpace
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.WindowClock
import TCSlib.Complexity.SpaceComplexity.Savitch
import TCSlib.Complexity.SpaceComplexity.Hierarchy
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi
import TCSlib.Complexity.SpaceComplexity.Logspace.Mult
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidthExample
import TCSlib.Complexity.SpaceComplexity.Machines.ARMReach
import TCSlib.Complexity.SpaceComplexity.Machines.NARM
import TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile
import TCSlib.Complexity.SpaceComplexity.Machines.NARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.NARMExample
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.VWord
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Codec.Word
import TCSlib.Complexity.SpaceComplexity.Codec.Scan
import TCSlib.Complexity.SpaceComplexity.Codec.Valid
import TCSlib.Complexity.SpaceComplexity.Codec.Step
import TCSlib.Complexity.SpaceComplexity.Codec.Langs
import TCSlib.Complexity.SpaceComplexity.Codec.Checks
import TCSlib.Complexity.SpaceComplexity.Codec.Engine
import TCSlib.Complexity.SpaceComplexity.Codec.Regs
import TCSlib.Complexity.SpaceComplexity.Codec.Machine
import TCSlib.Complexity.SpaceComplexity.Codec.Run
import TCSlib.Complexity.SpaceComplexity.Codec.Parse
import TCSlib.Complexity.SpaceComplexity.Codec.Layout
import TCSlib.Complexity.SpaceComplexity.Codec.Layout2
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Reach
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Machine
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Run
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Recursion
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Setup
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Search
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountMath
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountRegs
import TCSlib.Complexity.SpaceComplexity.Machines.MARM
import TCSlib.Complexity.SpaceComplexity.Machines.MARMCompile
import TCSlib.Complexity.SpaceComplexity.Machines.MARMTime
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Machine
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Run
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Relax
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Search
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Main
import TCSlib.Complexity.SpaceComplexity.ExpTime
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHard
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRegs
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardRun
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenWalk
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenCorrect

/-!
# Space complexity

Space-bounded computation and logarithmic space [AB09, §4.1, §4.3]: the classes `SPACE(s)`
and `L`, `L ⊆ P` by configuration counting, implicitly logspace computable functions and
their polynomial-time computability, with a toolkit of logspace machines (register-tape
programs calling logspace deciders on virtual inputs, and abstract register machines
compiled onto them).

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Contents

- `SpaceComplexity.Basic`: Def 4.1 space-bounded computation, `SPACE(s)`, `L`; Def 4.16
  implicitly logspace computable functions
- `SpaceComplexity.ConfigCount`: configuration counting; `L ⊆ P`; logspace functions run in
  polynomial time
- `SpaceComplexity.Machines.Layout`: virtual inputs assembled from segments
- `SpaceComplexity.Machines.Program`: register-tape programs with call nodes and their
  compilation
- `SpaceComplexity.Machines.Sim`: the lockstep simulation of a call's decider
- `SpaceComplexity.Machines.CallReturn`: compiled configurations; the return phase of a call
- `SpaceComplexity.Machines.Call`: the run of a call node
- `SpaceComplexity.Machines.Compile`: correctness and space of compiled programs
- `SpaceComplexity.Machines.CleanSweep`: the cleaned machine; the cleanup sweeps of one tape
- `SpaceComplexity.Machines.Clean`: the clean normal form of deciders (the whole run)
- `SpaceComplexity.Machines.Bank`: a bank of clean deciders
- `SpaceComplexity.Machines.Bin`: binary words of numbers
- `SpaceComplexity.Machines.Lib`: register steps and the increment fragment
- `SpaceComplexity.Machines.FragDec`: decrement and clear fragments
- `SpaceComplexity.Machines.Frag`: halve and equality fragments
- `SpaceComplexity.Machines.ParsePlain`: input shapes; the format check on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse`: comparisons on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse2`: the format check on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ParseCmp`: comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ARM`: abstract register machines and their compilation
- `SpaceComplexity.Machines.ARMSim`: per-instruction simulation
- `SpaceComplexity.Machines.ARMRun`: the run and space theorems of compiled machines
- `SpaceComplexity.Machines.ARMProof`: proving abstract machines correct; `arm_decides`
- `SpaceComplexity.Machines.ARMKit`: calls on unary inputs; `arm_decides_poly`
- `SpaceComplexity.Machines.ARMWidth`: abstract machines with wide registers;
  `arm_decides_space`, `arm_decides_SPACE`, `arm_decides_pspace`; `L ⊆ PSPACE`
- `SpaceComplexity.Machines.ARMWidthExample`: exhaustive search over `|x|`-bit witnesses
  with a polynomially wide register (`PSPACE` is closed under it)
- `SpaceComplexity.Machines.ARMReach`: compiled runs to live abstract configurations
  (`arm_step`, `arm_reach`)
- `SpaceComplexity.Machines.NARM`: nondeterministic abstract register machines (`choose`),
  their choice-word semantics and correctness combinators
- `SpaceComplexity.Machines.NARMCompile`: their compilation onto `FinNDTM`
- `SpaceComplexity.Machines.NARMRun`: the run and space theorems of compiled
  nondeterministic machines (`narm_space`)
- `SpaceComplexity.Machines.NARMProof`: `narm_decides_space`, `narm_decides` (`NL`),
  `narm_decides_npspace` (`NPSPACE`)
- `SpaceComplexity.Machines.NARMExample`: a guessing machine deciding a language in `NL`
- `SpaceComplexity.Machines.ARMLoops`: the bounded-run guard `GuardLe` and generic counting
  loops of abstract register machines
- `SpaceComplexity.Machines.VWord`: small shared lemmas on reading inputs by index
- `SpaceComplexity.Machines.NARMKit`: proving nondeterministic register machines correct by
  continuation (`NTerm`, `NAcc`, `NSem`), their step lemmas and generic nondeterministic
  loops
- `SpaceComplexity.Machines.DblLang`: reading the unary length `⟨1ⁿ, bits (2n)⟩` in
  logarithmic space
- `SpaceComplexity.ImplicitPoly`: implicitly logspace computable functions are
  polynomial-time computable
- `SpaceComplexity.UnaryLogspace`: functions of the unary length computable in logarithmic
  space (`UnaryLogspace`, `unaryExt`)
- `SpaceComplexity.CounterProgSim`, `SpaceComplexity.CounterProgSimRun`: polynomially
  running counter programs on unary-logspace inputs are unary-logspace
- `SpaceComplexity.NSPACE`: Def 4.1's nondeterministic clause, `NSPACE(s)` (chapters-3-4
  campaign, phase P4.1)
- `SpaceComplexity.SpaceClasses`: Def 4.5's `PSPACE`, `NPSPACE`, `NL`, and `coNL`
- `SpaceComplexity.Constructible`: space-constructible functions (p. 79)
- `SpaceComplexity.Inclusions`: Thm 4.2's first two inclusions; `P ⊆ PSPACE`;
  Example 4.6 (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)
- `SpaceComplexity.Examples`: Example 4.7's parity language
- `SpaceComplexity.ZeroSpace`: the zero-bound collapse of unnormalized `SPACE` and the
  positive-normalization identities (P0 reception audit, round 1)
- `SpaceComplexity.ConfigGraph`: configuration graphs and the ND Claim 4.4(1) (chapters-3-4
  campaign, phase P4.2; Thm 4.2(iii), `NL ⊆ P` and Ex 4.3 are in `SpaceComplexity.ExpTime`)
- `SpaceComplexity.WindowClock`: the windowed runner (host H3) under a configuration-count
  clock, window containment, and the windowed run of a halting space-bounded computation
  (the space hierarchy's window route; statement gate passed 2026-10-14)
- `SpaceComplexity.Savitch`: Savitch's theorem and `PSPACE = NPSPACE` (phase P4.2)
- `SpaceComplexity.Hierarchy`: the space-bounded universal machine, Thm 4.8,
  `L ⊊ PSPACE`, Ex 3.2 (phase P4.3)
- `SpaceComplexity.Logspace.{InputAccess, PreimageHost, QueryReshape}`: random access to a
  general input (a register-program read fragment; `id` implicitly logspace), the
  oracle-input simulator of Fig. 4.3 (logspace preimages along implicit functions), and the
  query reshapings of composition (phase P4.4b)
- `SpaceComplexity.Logspace.{Reductions, Path, ImmermanSzelepcsenyi, Mult}`: `≤ₗ` and
  Lemma 4.17, `PATH` and Thm 4.18, Thm 4.20 and Cor 4.21, `MULT ∈ L` (phase P4.4)
- `SpaceComplexity.Logspace.{PathWalk, PathWalkMachine, PathWalkProof}`: the
  nondeterministic walk deciding `PATH` (`PATH ∈ NL`, §4.1.2)
- `SpaceComplexity.Codec.{Word, Scan, Valid, Step, Langs, Checks}`: an `O(s + log n)`-bit
  codec for window-bounded configurations of a nondeterministic machine, the four code
  languages (valid, initial, accepting, step) and their word-level checks
- `SpaceComplexity.Codec.{Engine, Regs, Machine, Run, Parse, Layout, Layout2, Deciders,
  StepDecider}`: the four code languages are in `L` (an abstract register machine reading
  its input by index)
- `SpaceComplexity.Codec.Bridge`: acceptance of a space-bounded decider as a chain of codes
- `SpaceComplexity.SavitchARM.{Reach, Machine, Run}`: midpoint reachability over codes; the
  Savitch register machine and its arithmetic and stack routines
- `SpaceComplexity.SavitchARM.{Recursion, Setup, Search, Correct}`: the machine evaluates the
  midpoint recursion with an explicit stack; `NPSPACE ⊆ PSPACE` (Thm 4.14 at polynomial
  bounds, consumed by `PSPACE = NPSPACE` in `SpaceComplexity.Savitch`)
- `SpaceComplexity.Machines.{MARM, MARMCompile, MARMTime}`: abstract register machines with
  a monotone memory tape, their compilation, and their time bound by configuration counting
  (`marm_dtime`)
- `SpaceComplexity.ExpBFS.{Radius, Machine, Run, Relax, Search, Main}`: reachable codes at
  growing radii; the breadth-first search memory machine;
  `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c (S n + 1)))` for `S ≥ logSpace`
- `SpaceComplexity.ExpTime`: Thm 4.2(iii), `NL ⊆ P`, Ex 4.3 (moved from
  `SpaceComplexity.ConfigGraph`, after the codec)
- `SpaceComplexity.Logspace.{PathHard, PathHardRegs, PathHardMachine, PathHardWalk,
  PathHardRun, PathHardDecide}`: the configuration-graph reduction to `PATH`, the register
  file and deciders of its query register machine, the machine and its runs; every `NL`
  language logspace-reduces to `PATH` (Thm 4.18, consumed by `PATH_NLComplete` in
  `SpaceComplexity.Logspace.Path`)
- `SpaceComplexity.Logspace.{ISCountMath, ISCountRegs}`: the combinatorics of inductive
  counting (balls, guessed enumerations) and the register file of the counting machine
- `SpaceComplexity.Logspace.ISCountGen{Machine, Walk, Stage, Loop, Radius, Correct}`: the
  window-growing inductive-counting machine; `L ∈ NSPACE S → Lᶜ ∈ NSPACE S` for
  `S ≥ logSpace` (`compl_mem_NSPACE`, consumed by `NSPACE_compl_eq`, Cor 4.21) and its case
  `L ∈ NL → Lᶜ ∈ NL` (`compl_mem_NL`, consumed by `compl_PATH_mem_NL` and `NL_eq_coNL`,
  Thm 4.20)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/
