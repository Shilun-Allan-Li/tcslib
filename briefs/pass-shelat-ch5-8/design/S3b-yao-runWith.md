# S3b route note: Yao's garbled evaluation through `DAGCircuit.runWith`

Status: **route probed, 2026-11-04.** The probe is `probes/S3b-garble-runWith.lean.txt` and its
output is `probes/S3b-garble-runWith.out.txt`. It elaborates with no errors and no warnings, and
`runWith_sim` prints the standard axioms. It was checked against `main` at
`06e61e912eedc2bce49b3ccff77bb9c4a7e18579`; `DAGCircuit.lean` is identical on
`cryptography/pass-shelat-ch2-4`.

## The question

[PS10] §6.2.1–6.2.3 (Constr-158.a, Claim-159.a) garbles a fan-in-two circuit:
- every wire gets two keys;
- every gate gets a randomly permuted table of output keys, doubly encrypted under the input keys;
- the evaluator holds one key per input wire, opens one row per gate, and ends with the keys of
  the output wires.

The spine proposes to reuse `main`'s `BoolCircuit.DAGCircuit`, whose `runWith f gs init` folds a
gate list over data of any type. Can garbled evaluation run through the same traversal as Boolean
evaluation, and is correctness then a simulation lemma between two `runWith` instances?

## Finding: yes, with one design point

**`runWith`'s gate function does not receive the gate's index**: `f : DAGGate → List β → β`. A
garbled gate needs its own table, but the index is recoverable from the data. When gate `i` is
processed, the list already holds `n + i` entries (`length_runWith`). So the garbled evaluator is
`runWith (fun g vs => evalGarbled (vs.length) g vs) C.gates initKeys`, with `evalGarbled v`
reading the table of vertex `v`. **No change to `main`'s file is needed.**

**The simulation lemma** `runWith_sim` (probed, about 30 lines) relates two `runWith` runs:
- the hypotheses are a per-vertex encoding `W v : α → β`, here `W v b` = the key of wire `v` for
  bit `b`;
- and a per-gate hypothesis: on data encoding the Boolean data at the gate's inputs, the garbled
  gate outputs the encoding of the Boolean gate's output;
- the conclusion is that the two runs agree through `W` at every vertex.

The proof is strong induction on the vertex. It uses only `main`'s published equations
(`runWith_getD_of_lt`, `runWith_getD_gate`, `runWith_getD_take`, `length_runWith`), so it
satisfies rule 10. Acyclicity enters as `DAGCircuit.args_lt`. A one-gate instance (an `∧` gate
garbled as an ideal lookup table) is in the probe.

## What this gives prong B

- **Claim-159.a (garbled evaluation correctness)** splits into:
  1. the per-gate statement: with the right input keys, exactly one row decrypts, to the right
     output key. This holds with high probability, via Alg-157.2's "a wrong key gives `⊥`"
     (Claim-157.a);
  2. `runWith_sim`, which is deterministic.

  The probabilistic part is a union bound over gates and rows of the per-gate failure event.
- **Gate fan-in.** `DAGGate` allows any fan-in, and `¬` is "NAND of its inputs". Garbling takes
  `C.IsFaninTwo` as a hypothesis, giving tables of `2^{|args|} ∈ {1, 2, 4}` rows; fan-in 0 is the
  constant gates `constGate`. [PS10]'s fan-in-two circuits are the case `|args| = 2`.
- **Where it lives.** `runWith_sim` is generic in the circuit model. It belongs beside `runWith`
  in `main`'s `DAGCircuit.lean`, which is not ours, or in a new file of the B prong
  (`SecureComputation/Garbling/Simulation.lean`) with a request to move it. **Proposed:** the new
  file, plus a note in the B prong's PR asking the circuit file's owner whether to move it.

## Open points (for the S4 statement phase)

1. The garbled-table type: rows as ciphertexts of Alg-157.2's special encryption, with the table
   permuted by a uniform permutation of `Fin (2^{|args|})`. That permutation sits in the coins of
   the garbling algorithm, as a finite uniform seed (`uprob`), consistent with S2.
2. The output decoding: [PS10] has A send the output-wire key table, or B send back the output
   keys. Fix this together with Prot-162.6.
3. Thm 163.7 needs a hybrid over gates. Its order follows the topological order of
   `DAGCircuit.gates` (Gol04 §7.3's argument). The S2 framework carries the hybrid steps.
