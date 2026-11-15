# seq-zk-b padded-prover construction contract result

The approved SequentialZK.PaddedProverSpec π ρ x q p structure and its direct methods
real_phase / padded_phase compile without admissions. The nine field names are:
prover_coinLen, rounds_eval, first, next, prover_index, boundary, original_count, real_le,
and period. The index and boundary readers hold at all natural indices/phases and against
every verifier. The contract carries no relation/message-bound premise.

The main owned instantiation may choose numeric p = if π.verifierFirst then k/2 else
(k+1)/2, k=π.rounds.eval |x|, matching SimulatorMachine. The two endpoint methods reuse
checked RealPhases directly; no phase, filler, or arithmetic proof is repeated.

Final source: 142 lines, maximum width 94, SHA256
9f8db36d78ede79900e5016a102559d16e6b84478079c4a9c4723a2292ee5d35.
check-02: exit0, no diagnostics, runtime2.38s, maximum RSS2219655168 bytes.
The structure, constructor and all nine projections use only propext; both endpoint methods
use only propext and Quot.sound. Complete probe source/output retained; no sorryAx.
Final style lint across ten local helpers: 0 FAIL / 0 WARN.

check-01 retained 12 parser diagnostics for capital Π, which is Lean syntax rather than a
binder identifier. The lead correctly identified this while the check was still queued;
the source was kept unchanged until that attempt exited, then renamed consistently to ρ.
The exact initial source snapshot was reconstructed by the sole inverse character change,
and its SHA256 was checked against the initial static record before retention.
No proof-statement or contract-field changes were required.

The structure is the prover-side counterpart of seq-zk-c's PaddedVerifierSpec, explicitly
disclosed in padded-prover-spec-overlap.md with source searches and all method relatives.
No previous stable helper was changed, no foreign source/olean was copied for this module,
no host was introduced, and no frozen-file edit or commit was made. All Lean runs used the
required tag/wrapper and seq-zk-b's private olean tree, host-wide cap3. The lead retains final
merged verification and all-stored-constant/whole-closure seal responsibility.
