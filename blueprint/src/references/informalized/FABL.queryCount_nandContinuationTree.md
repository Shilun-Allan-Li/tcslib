<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.queryCount_nandContinuationTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAND continuation query count

**Claim.** For a first sign \(a\), a decision tree \(T\), and input \(x\), the NAND continuation makes no queries if \(a=1\), and otherwise makes as many queries as \(T\).

**Proof.** A sign is either \(1\) or \(-1\). If the first sign is \(1\), the continuation is a leaf, so its query trace is empty and its count is zero. If the first sign is \(-1\), the continuation is \(T\) with its output relabelled by the NAND operation. Relabelling leaves does not alter which coordinates are queried, so its query count equals that of \(T\).
