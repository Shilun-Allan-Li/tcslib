# Fill brief (DRAFT, not issued): the efficiency of reductions (`Games/Efficiency.lean`)

Status: **draft, 2026-11-05.** Ruled: a Claude fill on the GGM reduction machine's pattern, issued
after gate 02 closes. Still to come before issue:
- the Lean skeleton of the targets (statements with `sorry` under literal proof sketches), written
  by the maintainer and elaborated on the issue tree;
- the pre-ship probes (import probe of every cited name; a route probe of the generic loop on a
  toy handler; a duplication probe);
- the order list and Mathlib roots;
- a review of this brief by a review sub-agent;
- the issue commit (`@ANCESTOR@`).

The route note is `briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`; read it first.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib`, and check out the branch named at issue
  (the S2b branch, stacked on the `Games` core). The issue commit is `@ANCESTOR@`.
- Create your working branch from it (suggested name `fill/s2b-efficiency`). Record the base hash
  in `REPORT.md`, and never rebase.
- **Delivery is by zip**, `fill-s2b-efficiency.zip`, with the standard contents: `REPORT.md`, the
  owned file, a `git format-patch` series, a git bundle, the sweep log, the axiom prints and
  `SHA256SUMS`.

## What this is

A reduction runs a machine adversary `A` and answers `A`'s oracle queries with a polynomial-time
handler. The targets say the result is again a machine's computation, so hardness assumptions
quantified over machines (`Complexity.NUPPT`) apply to it. Two targets:
1. **Simulation inside a plain machine** (the reduction makes no oracle queries of its own;
   example: GGM, or Lamport from a one-way function).
2. **Simulation by an oracle machine** (the handler queries the reduction's own oracles; example:
   a MAC from a PRF, or CPA security of [PS10, Alg 99.1]), by **log replay**. The reduction's
   next move recomputes the simulated interaction from its own log, and stops at the first
   handler query not yet answered.

## The template you must follow (cite; do not copy)

Frederick Dehmel's GGM reduction machine, `TCSlib/Cryptography/Asymptotic/GGMReduction.lean` and
`GGMReductionEval.lean`, is this construction for one handler (a lazily sampled table). Reuse
verbatim, by citation:
- `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval`, the generic state loop
  with a length-guarded step;
- `Complexity.polyTimeComputable_iterateFind`, `StateLoop.gstep` and their bounds;
- `NUPPT.polyTimeComputable_output`, `NUPPT.ofPolyTime`, and the closure calculus
  (`Complexity/Randomized/Closure.lean`: `exists_split`, `exists_seq`, `exists_withAdvice`);
- the pairing calculus (`ClassNP/PolyTimePairing.lean`).

Generalize **by analogy**: `GGMRed.step`, `rawFun`, `rawFun_poly`, and the evaluation identity in
`GGMReductionEval.lean` (`firstRound`, `rawFun_rawInput`, `ggmRedMachine_distinguisher`).

## Fixed lengths (the design constraint)

Oracle queries and answers, the adversary's output and the handler's state are **fixed-length bit
strings**, with polynomial lengths:
- query and answer lengths are `din i`, `dout i : PolyExpr` for `i : Fin k`;
- the output length is `dα : PolyExpr`;
- the state length is `dσ : PolyExpr`.

This bounds every history by `q(n)·(max lengths + c)`, so the guarded loop never fires on a
genuine run (GGM's `length_encState_pureAt_le` pattern). Do not generalize to variable lengths.

## Targets (statements frozen at issue; exact Lean in the skeleton)

- **T0 (definitions, maintainer-written):**
  - `bitSpec`: the fixed-length family;
  - `bitCodec`: decoding of moves (a tagged oracle index and query) and encoding of log entries;
  - `PolyHandler`: a polynomial-time `H : List Bool → List Bool` on
    `⟨⟨1^n, ω⟩, ⟨s, ⟨i, x⟩⟩⟩ ↦ ⟨y, s'⟩` (non-interactive), or a next-move form that may ask the
    target oracles (interactive);
  - its semantics as a `Games.QueryImpl`, indexed by the seed `ω : Fin (seed.eval n) → Bool`.
- **T1 (non-interactive):** for every NUPPT `A`, budget `q` and `PolyHandler` `H`, there is a NUPPT
  `B` and, for each `n`, a bijection `φ` from (seed, `A`'s coins) to `B`'s coins, such that `B`'s
  output at `n` on coins `φ (ω, r)` equals the output of the simulation of
  `A.toComp bitCodec n (q.eval n) r` by `H`'s implementation under `ω`.
- **T2 (interactive):** the same, with `B` an oracle machine: `B.toComp bitCodec' n (q'.eval n)
  (φ (ω, r))` equals the simulation (outputs only). The target budget is `q'(n) = q(n) · c(n)`,
  where `c` bounds the handler's queries per call.
- **T3:** `GGMRed`'s machine is an instance of T1. It is stated, **not proved** in this fill, and
  goes to the integration of ch. 2–4, coordination point F-4. Leave it as `sorry` under its
  sketch only if the skeleton contains it.

## Ground rules (binding)

1. **Statement freeze:** T0's definitions and T1–T2's statements are byte-identical in your
   delivery.
2. **Rule 10:** read other files' definitions only through published equations. `GGMRed`'s and
   `NUPPT`'s public lemmas are the interface. Seal-check your proofs.
3. **Reuse, not copy:** do not copy GGM's proofs. If a lemma you need is private there, request
   it in `REPORT.md` and reprove a generic version under your own prefix, listed in the ledger
   line.
4. **Escalation:** a target that looks false as stated (for example from a missing length
   hypothesis) is reported, never patched.
5. **Budget:** T1 complete beats T1 and T2 partial.

## Environment and verification

Use the environment addendum (attached at dispatch) and **never `lake build`**. Fetch the Mathlib
cache for the order list's roots only. Final checks:
- `Games/Efficiency.lean` with zero errors and zero sorry warnings (except T3);
- axiom prints for T1 and T2: at most the standard triple;
- lint 0 FAIL on the owned file.

## REPORT.md checklist

- [ ] T1, T2 (complete or partial, with a frontier); the base hash.
- [ ] Every new `private`, with its role.
- [ ] The reuse-not-copy screen: what is cited from `GGMRed`, what is new, and any requests.
- [ ] The final sweep tail, the axiom prints, and the lint line.
- [ ] The diff touches only the owned file.

## Known pitfalls (from the GGM machine and the S2 probes)

- History lengths: prove the genuine orbit fits the guard bound (`gstep` refuses to move
  otherwise); this is where a missing fixed-length hypothesis shows up.
- The coin layout: `A`'s coins and the seed are split with `exists_split`; the bijection `φ` is
  part of the statement, as in `exists_queryChain_nuppt`.
- `buildComp` unfolds by `match` on the decoded move. Prove the functional equation by induction
  on the remaining budget along the genuine history (`buildComp_singleCodec`'s pattern in
  `Games/Machines.lean`).
