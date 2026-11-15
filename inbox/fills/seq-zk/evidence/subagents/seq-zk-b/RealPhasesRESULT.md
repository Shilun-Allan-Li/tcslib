# seq-zk-b real-phase endpoint result

All three public theorems of SequentialZK/RealPhases.lean are proved and checked:
exec_snd_empty, exec_real_phase, and exec_padded_real_phase.
The source is 207 lines, maximum width 95, SHA256
8fbb770a0dd689155308856dfc177479d055fd8e60108aaf26a9773dc19e4f17.
Both module attempts passed with no diagnostics; final attempt 2.99 seconds, max RSS
2265055232 bytes. All three axiom prints use only propext and Quot.sound, with no sorryAx.
Style lint across the nine local helpers: 0 FAIL / 0 WARN.

The real phase directly reuses seq-zk-c's checked exec_phase_of_moves, and identifies
original P on prover coin block j against phaseVerifier V with the canonical phaseAux of
the fixed earlier received-prover prefix. Generic prefix/take readers prove the arbitrary
verifier contract. The full padded endpoint appends exactly the real messages and k-p empty
honest-prover fillers. The verifier's filler replies are unrestricted. There is no extra
positive-round, positive-count or parity hypothesis; zero rounds are covered by the empty
execution, and the original real-message count p is supplied explicitly.

Every overlap, including local division/remainder arithmetic relatives in the owned source,
is disclosed in real-phases-overlap.md. The generic filler induction is distinct from and
does not duplicate the imported real-phase transport induction. No frozen file was edited.
Dependency source-only copies, hashes, independent checks, probe sources, raw output and
all diagnostic counts are retained under this sub-agent evidence directory.
All Lean commands used seq-zk-b's isolated olean tree and host-wide slot wrapper/tag, cap3.
No Lake command, foreign olean copy, new host, or commit occurred.
