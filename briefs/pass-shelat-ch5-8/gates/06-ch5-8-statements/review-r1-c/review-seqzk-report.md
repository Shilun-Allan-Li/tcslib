# Gate06C C-03: sequential ZK and 3COL

**C-03 is a confirmed minor sketch gap.** The proposed count-and-length normalization gives a viable strict-PPT composition plan under the current premises. No additional theorem premise or ruling is needed for this correction identified here. This is a bounded source review, not proof completion or gate/merge clearance.

Frozen source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Received report: SHA256 `577621ca9f6fa665dbc6bd3150f4625ddf2b05d19b9f6021bf652c30c8580ac4`, archived at records `636609a032bd48899dd5adbc3752353a3b2efc66`. Reviewed C-03, the relevant repetition/model declarations and 3COL corollary; no independent re-audit of the other C findings or primary PDFs is claimed.

## Actual slots, not a guessed transcript shape

In `SequentialZK:200–258`, a phase has **2k moves**. The verifier receives exactly **k prover messages** in a complete padded phase. Of these, `p = proverMoves π.verifierFirst k` are sent in the first k real moves; the remaining **k-p** are the honest repeated prover's `[]` fillers. The execution model always counts turns, including empty messages (`Interaction:247–264`).

`View` contains the party's input, auxiliary input, tape and **received** messages (`Interaction:279–298,450–467`). Thus the repeated verifier's view contains prover messages, not its own replies. **Only honest-prover fillers are canonical empty slots. A cheating verifier's filler replies remain unrestricted.** The honest prover's next real phase drops the previous received prefix, so this distinction is consistent with the actual schedule.

The old sketch caps each word at B(n) but leaves the list count uncontrolled. Many empty words already have a large `encodeMsgs` representation: each adds two framing bits. A rare simulator branch can therefore cause a rapidly growing auxiliary prefix despite every word being empty. Positive but negligible probability does not satisfy a worst-case strict-PPT running-time bound.

## Total normalization supports the existing premises

Use one deterministic efficient phase-verifier wrapper whose auxiliary input holds the original z, global verifier tape r, phase index and previous received-prover prefix. Its own tape is empty. For each simulated phase, syntactically parse the view/message encoding; normalize to **exactly p real slots**, truncating every word to B(n) and padding missing entries with `[]`. Reuse the known phase metadata. A bad/noncanonical encoding or unexpected metadata maps to the fixed canonical phase view with p empty real slots. Append exactly k-p prover fillers. No witness or semantic transcript-validity test is required.

This transformation fixes every real phase view: its metadata and count are fixed by the experiment, and `Protocol.ProverBounded` bounds every honest prover message for **all** tapes and histories on a witnessed instance (`Interaction:355–363`). It does not assume a computational/statistical simulator already returns a well-shaped view. Every resulting phase has k slots of length ≤B(n), so every retained prefix has at most Q(n)k slots and encoding length ≤Q(n)k(2B(n)+2). The proposed comments include the original auxiliary input, tape, phase-index and fixed pairing overhead rather than retaining the old overly literal auxiliary-length expression.

For each auxiliary-input polynomial Lz, the phase inputs therefore fit another polynomial Lz'; the simulator itself remains the same uniform program and runs in polynomial time in n+|z|. Its per-phase fresh coin blocks and global verifier tape have fixed polynomial lengths. For k=0 or Q(n)=0, output the exact empty-history view with a fresh verifier tape directly. B(n)=0 and empty coin blocks need no new positivity or nonemptiness premise.

For statistical composition, apply the same total normalization/simulated-suffix processing on both sides of a phase comparison. It fixes the real distribution and cannot increase the existing δ(n) distance; mixing over fixed prefixes and summing gives exactly Q(n)δ(n). This includes δ=0, so the perfect specialization is preserved. For computational composition, the allowed nonuniform distinguisher can hardwire a maximizing phase/prefix and bounded x,z,r as polynomial advice. It need not simulate an inefficient honest prover, know its witness, or trust malformed simulator metadata. The usual Q(n)ε(n) hybrid bound then has the same assumptions as the current statement. These are proof-plan arguments; the admitted generic bodies remain unfilled.

## 3COL uses precisely this shape

Actual `colProtocol` has **three moves, prover first** (`ThreeColoring/Protocol:468–472`). Each padded six-move phase contributes **two real prover messages plus one empty prover filler** to the verifier's view. Normalizing to three *real* messages and then adding a filler would be wrong.

The corollary already obtains `hB` from `col_efficientProverProofErr hC` and passes it to `ZK.seqRep` (`Composability/ThreeColoring:128–132`; base boundedP at Protocol:974). It adds no premise to Commitment and no simulator-shape guarantee. Q remains `2(N+1)^2`; the eventual numerical proof and its treatment of N=0 are unchanged. Generic repetition admissions are still dependencies of the corollary.

## Concrete comment-only proposal

`seqzk-phase-normalization-comments.patch` updates the ZK and StatZK sketches in SequentialZK and the application sketch in ThreeColoring. SHA256: `5292416d91d6c1be5b06307d130a601f2b8e0d5b58e264e9c453e37c48e3099e`.

Exact frozen and proposed snapshots are under `frozen-source/` and `proposed-source/` as `.lean.txt` files. **Noncomment bytes are exactly equal for both modules**: every definition, public claim, import, proof and admission is unchanged. SequentialZK keeps its five direct `sorry` bodies; ThreeColoring keeps none. The proposal adds no public API, algorithm, statement, proof fill or source guarantee.

Own Python-I data checks passed: 132 schedule cases, 792 malformed/missing/excess/oversize/zero normalization cases, 132 real-phase fixed-point cases and 4,752 prefix-encoding cases, plus exact source/code/admission/report hashes (11 checks total). These finite tests are arithmetic/model sanity checks, not kernel proofs or a simulator implementation. No Lean/native/build/cache/app command, incoming-script execution or tracked source/main/exchange/Git mutation occurred. The patch remains unapplied.
