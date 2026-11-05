# Bridges between the crypto model (NUPPT) and `TCSlib/Complexity/`

Survey of 2026-11-05, at the user's question. "Branch" is `cryptography/pass-shelat-ch2-4` (forked
from `main` on 2026-10-08); "main" is `origin/main`.

## What exists

| Bridge | Where | Direction and strength |
|---|---|---|
| **FP (`Complexity.PolyTimeComputable`)** | `Randomized/PPT.lean`, `Closure.lean` (branch) | Both ways. `NUPPT.polyTimeComputable_output` (a machine's output function is FP) and `NUPPT.ofPolyTime`/`ofPolyTimeUniform` (every FP function is a machine's), plus `Computes.polyTimeComputable` and the closure calculus. `PolyTimeComputable` is `main`'s own notion (`ClassNP/PolyTime.lean`), the one `P`, `NP` and the reductions are built on. **This is the backbone:** anything deterministic and polynomial-time on `main` enters the crypto layer through it. |
| **NP and Karp reductions** | `ZeroKnowledge/NP.lean`, `InteractiveProofs.lean` (branch) | The ZK layer is stated against `main`'s `NP`, `PClosure` and `≤ₚ`. `LevinReduction.polyTimeReducible` maps Levin to Karp reductions, and [PS10, Thm 124.1] is stated for `main`'s NP. |
| **Advice** | `Randomized/NonUniform.lean` (branch), importing `CircuitComplexity/Advice.lean` | One way: `decides_of_decidesWithAdviceInTime` turns `main`'s advice deciders into NUPPT deciders. |
| **The universal machine; padding** | `Asymptotic/Universal.lean`, `Asymptotic/Collections.lean` (branch) | Used directly (`TuringMachine/Universal`, `PolyHierarchy/Padding`). |
| **Probability (crypto side)** | `Games/Bridges/Experiments.lean` (S2b) | Garg's `uprob` functionals are probabilities of `Games` computations. |

## What is missing

| Gap | Matters for | Notes |
|---|---|---|
| **Randomized classes** (ch7: `InBPP`, `InRP`, `InZPP`, `PTM`, `polyTimeModel`, `randProb`) | prong D, Thm 180.1 | None exist: the branch forked before ch7 reached `main`. D-6 plans one direction (a `polyTimeModel` BPP verifier gives a NUPPT; `randProb` (ℚ) equals `uprob` (ℝ)), in `design/S3c-bpp-bridge.md`. |
| **Uniform circuits for polynomial-time functions** | prong B (Yao: the garbler must compute the circuit of `f` in polynomial time) | `main` has the pieces: `Language.mem_P_iff_exists_isPUniform` and the tableau family (`CircuitComplexity/UniformTableau.lean`), circuit evaluation in `P` (`PUniformP.lean`, `CircuitEval*`), and fan-in transforms (`DAGFanin.lean`). Still unbuilt: from an FP function (multi-bit output) to a P-uniform **fan-in-two** `DAGCircuit` family computing it, via each output bit's language. This is prong B's statement-phase obligation. |
| **Oracle machines** (`ClassOracle`, `TuringMachine/Oracle*`, `Build/OracleSim`) | none directly | A different machine model (oracle tapes, language oracles); see `S2b-efficiency.md`. |
| **P/poly and circuits as adversaries** (`PPoly`, `P_subset_PPoly`) | none in ch. 5–8 | NUPPT advice is the crypto layer's non-uniformity; a NUPPT ↔ circuit-family bridge is not needed for the inventory. |
| **Two probability models** | prong D | The crypto side uses ℝ (`uprob`, `FinDist`, `Games.ProbComp`); ch7 uses ℚ (`randProb`, `PTM.outputProb`). D-6's small lemma covers `randProb`; `PTM.outputProb` is not needed. |

## The practical bottleneck

Every missing bridge that ch. 5–8 needs, for the randomized classes (prong D) and the uniform circuits
(prong B), connects to `main` material **not on the branch**. Merging `main` into
`cryptography/pass-shelat-ch2-4` (S1 point 5, Frederick's agreement) gates both, and prong B and
Thm 180.1 are the two prongs ruled first. A scratch merge showed it costs two trivial textual
conflicts and no name clash (`S3c-bpp-bridge.md`).
