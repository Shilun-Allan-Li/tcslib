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
import TCSlib.Complexity.SpaceComplexity.Savitch
import TCSlib.Complexity.SpaceComplexity.Hierarchy
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi
import TCSlib.Complexity.SpaceComplexity.Logspace.Mult

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
- `SpaceComplexity.ConfigGraph`: configuration graphs, the ND Claim 4.4(1), Thm 4.2(iii),
  `NL ⊆ P`, Ex 4.3 (chapters-3-4 campaign, phase P4.2)
- `SpaceComplexity.Savitch`: Savitch's theorem and `PSPACE = NPSPACE` (phase P4.2)
- `SpaceComplexity.Hierarchy`: the space-bounded universal machine, Thm 4.8,
  `L ⊊ PSPACE`, Ex 3.2 (phase P4.3)
- `SpaceComplexity.Logspace.{Reductions, Path, ImmermanSzelepcsenyi, Mult}`: `≤ₗ` and
  Lemma 4.17, `PATH` and Thm 4.18, Thm 4.20 and Cor 4.21, `MULT ∈ L` (phase P4.4)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/
