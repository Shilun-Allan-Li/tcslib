# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Reading Files
Always use read only commands such as grep, cat, etc. Don't use commands such as sed.

## Project Overview

tcslib is a Lean 4 formalization of coding theory, including classical and quantum error correcting codes, and Boolean function analysis. It depends on Mathlib4.

## Build Commands
If you are a claud agent, use the VS code IDE to see build and lean4 server info.

## Debug
Use the VS code IDE to see the error message to debug.

## Lean Toolchain

The project uses `leanprover/lean4:v4.25.0-rc2` (see `lean-toolchain`). Lean is managed via elan.

## Code Style Rules (enforced by CI)

- Lines must not exceed **100 characters** in `.lean` files (URLs are exempt)
- **No bare `import Mathlib`** — use precise imports only (e.g., `import Mathlib.LinearAlgebra.Matrix.Determinant`)

## Architecture

The main library lives in `TCSlib/` and is structured as:

### `TCSlib/CodingTheory/Basic.lean`
Core classical coding theory. Key definitions:
- `Codeword n α` — functions `Fin n → α` over an alphabet `α`
- `Code n α` — finite sets of codewords
- `hamming_distance`, `weight` — Hamming distance and weight
- `distance C d` — predicate that code `C` has minimum distance `d`
- `rate C` — code rate (`log |C| / (n * log |α|)`)
- `Linear_Code` — linear codes via generator matrix

Key theorems: `singleton_bound`, `hamming_bound`, `hamming_ball_size`, `Linear_Code_dist_eq_min_weight`, `gv_bound`, `list_decoding_capacity`.

### `TCSlib/CodingTheory/QuantumSingleton.lean`
Quantum error correcting codes in the symplectic formulation:
- `V n p` — symplectic vector space `F_p^n × F_p^n` (p prime)
- `sym_form` — standard symplectic form
- `IsIsotropic S` — isotropic submodule predicate
- `correctable`, `code_k S` — error correction and logical dimension

Proves the quantum Singleton bound.

### `TCSlib/CodingTheory/QuantumHamming.lean`
Quantum Hamming codes:
- `Hn n` — quantum state space for n qubits
- `PauliNZ`, `pauliStringsExactSupport` — Pauli operator algebra
- `codeProj`, `error_sphere_dimension` — code projector and error subspace

Proves `quantum_hamming_bound`.

### `TCSlib/BooleanAnalysis/Basic.lean`
Boolean function analysis over `{0,1}^n`:
- `BoolCube n` ≡ `Fin n → Bool`, `BooleanFunc n` ≡ `BoolCube n → ℝ`
- `expect`, `innerProduct` — uniform expectation and L² inner product
- `chiS S` — Walsh-Fourier character χ_S
- `fourierCoeff f S` — Fourier coefficient f̂(S)
- `influence i f`, `totalInfluence f` — coordinate influences
- `noiseOp ρ f` — noise operator T_ρ

Key theorems: `walsh_expansion`, `parseval`, `influence_eq_sum_fourier`, `totalInfluence_eq_sum_sq_deg`, `stability_formula`.

## Blueprint (Mathematical Documentation)

The project maintains a LaTeX blueprint in `blueprint/` that generates web and PDF documentation linked to Lean declarations.
