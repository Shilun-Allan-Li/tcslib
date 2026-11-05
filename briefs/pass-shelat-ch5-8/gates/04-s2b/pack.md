# Gate 04 (Pass–shelat ch. 5–8, S2b): external API audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in when the S2b PR
is opened (after the dedup PR lands).

**What is audited:** the S2b layer of the `Games` framework on `cryptography/pass-shelat-ch5-8-s2b`,
at `<HEAD, 40 hex>`. It connects the framework core (S2a, gate 02, closed) to the machine model and
to the ch. 2–4 layer.
- **Gate type:** an **API gate** (user's ruling of 2026-11-04: one API gate each for S2a and S2b).
  Every statement of prongs A–D will be written against this layer.
- **The deliverable:** **`gate04-s2b-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] (PDF). Book page = PDF page − 12.

## What S2b contains

| Piece | Files | Ruling |
|---|---|---|
| **F-1:** oracle adversaries restated at the root. `QueryTree I O α` *is* `OracleComp (singleSpec I O) α`, with match-pattern constructors and `QueryTree.induct`; universes go to `Type`. | `Pseudorandom/Functions/{OracleAdversary, LazySampling, Defs, SubHybrids, GGM}.lean`, `Asymptotic/{PRF, PRFLemmas, MultiMessage, MultiMessageLemmas}.lean`, `Games/OracleComp.lean` | 2026-11-05 |
| **B1:** query trees in the framework. Evaluation, simulation and query bounds are the framework's. | `Games/Bridges/QueryTree.lean` | R-2 |
| **B2:** the concrete experiments as games, read through the new defining equations (F-3). | `Games/Bridges/Experiments.lean`, `Foundations/{Experiments, Probability}.lean` | R-2 |
| **B3:** machines as oracle computations: `Move`, `MachineCodec`, `buildComp`, `NUPPT.toComp`/`toCompOn`; the ch. 2–4 next-query machines are an instance. | `Games/Machines.lean`, `Games/Bridges/Machines.lean` | — |
| **The bit-string codec:** the shared codec of every prong's security games (efficiency T0). | `Games/BitCodec.lean` | — |
| **The efficiency layer:** `PolyHandler` and its semantics; T1 stated; `InteractiveHandler` (a handler that queries outer oracles, at most `perCall(n)` times per call) and T2 stated, for the efficiency fill. | `Games/Efficiency.lean` | 2026-11-05 (fill after gate 02; T2 added the same day, needed by the reductions of Thms 135.4, 144.1, 168.2, 170.4) |
| **B4:** next-message strategies embedded as parties. The embedded execution is D8's (`exec_strategies`). | `Games/Bridges/Strategies.lean` | 2026-11-05 (strategies define, the framework proves) |
| **Trace invariants** of `execT` (gate 02, round 2, note 5) | `Games/Protocols.lean` (`execT_trace`), `Games/OracleComp.lean` (`AllOutputs`) | — |

## Brief for the auditor

As for gate 02 (the API gate of S2a): restate every new or changed definition in your own words
before reading its docstring, and say in 1–3 sentences whether each theorem's statement is what
its docstring claims. Attempt at least **three adversarial instantiations**. Do not give a blanket
approval. Also:
1. **F-1 must not change meaning.** Check that every restated declaration of the concrete layer
   and of `PRF.lean` means what it meant before, against the pre-F-1 sources (in the bundle as
   `pre-F1/…`). The universe restriction to `Type` is a declared deviation.
2. **The codec must be faithful.** Check that `bitCodec` decodes exactly the well-formed moves,
   that its defaults are harmless, and that `decodeIdx`'s unary index cannot be gamed.
3. **T1 and T2 must be usable contracts.** Check that `exists_handlerMachine` (and its
   interactive form `exists_interactiveHandlerMachine`, with an oracle machine `B` of budget
   `q(n) · perCall(n)`) says what a reduction needs:
   - `B` is a machine;
   - its coins split as `(seed, A's coins)` by a bijection;
   - its output is the simulation's.

   Report any hypothesis that is missing (for example, length bounds) or vacuous.
4. **B4 must be D8's execution.** Check `exec_strategies` against `Protocol.outP`/`outV`, and
   check that the embedding's off-schedule defaults never matter for embedded pairs.

## Attestations (maintainer execution claims; evidence under `evidence/`)

To be filled at the pinned head. Already measured on the S2b work-in-progress head
`e72acc2ad7275bcb459705a2fce19427b42a9138`:
- **Elaboration:** a fresh-tree ladder over the 371 modules downstream of the changed files (with
  upstream), then the 5 new S2b modules and the facade: all pass, with 0 errors.
- **`sorry`:** one, `Games.exists_handlerMachine` (T1, the efficiency fill's target). At the pinned head: two, with T2 (`exists_interactiveHandlerMachine`).
- **Axioms:** 87 theorems across the S2b files. Only T1 depends on `sorryAx`; the other 86 use only
  `propext`, `Classical.choice` and `Quot.sound`.
- **Lint:** 0 findings on the new files.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in gate 02. The gate closes at **0 blockers and 0 majors**.
