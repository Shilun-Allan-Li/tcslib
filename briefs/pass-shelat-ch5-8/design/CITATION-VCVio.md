# Citation for the S2 game framework's design source

Ruled 2026-11-04 (user): S2 is home-built at TCSlib's pins, **adapting VCVio's design**, and VCVio
**must be cited**. `policy.md` (§2, *Design adaptation*) requires the citation even though no code
is transcribed: in the `## References` of every module that uses the adapted design, with a short
tag usable at declaration level, and in every design document and blueprint entry built on it.

## The reference block (use verbatim in module docstrings)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
```

## Declaration level

A declaration whose shape follows a VCVio construction carries `[VCVio, <module>]` in its
docstring, for example `[VCVio, OracleComp/OracleSpec]`, after the source citation ([PS10], [KL],
[Gol04]) that the mathematics comes from.

## What is and is not taken

- **Taken (design):** the three ideas above.
- **Not taken:**
  - no code, and no proof;
  - not VCVio's probability semantics: TCSlib keeps real-valued probabilities over finite uniform
    seeds (`uprob`) and `FinDist`;
  - not its notion of polynomial time: TCSlib keeps the Turing-machine `Complexity.NUPPT`;
  - not its program logic or tactics.
- **Why not a dependency:** VCVio pins Lean 4.35.0 with Mathlib v4.35.0, while TCSlib pins Lean
  4.25.0. Its polynomial time is a backend-relative cost model, and its probability semantics is
  measure-valued (the decision log of `PassShelatChapter5-8Plan.md`, 2026-11-04).

## Authors seen in the consulted modules (from their headers)

Checked at the pinned commit (gate 02, finding 7):
- `OracleComp.lean`, `ProbComp/Basic.lean`, `SimSemantics/QueryImpl/Compose.lean`: Devon Tuma,
  Quang Dao;
- `OracleSpec.lean`, `OracleQuery.lean`: Devon Tuma;
- `QueryTracking/LoggingOracle/Core.lean`: Devon Tuma, Quang Dao, Alexander Hicks.

The repository has since moved to `https://github.com/Verified-zkEVM/VCVio`; the old URL
redirects, and the citation keeps it, with the pinned commit.
