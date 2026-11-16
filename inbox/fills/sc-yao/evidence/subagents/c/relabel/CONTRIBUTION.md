# Subagent c: exact coin-block relabeling

Source: `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean`.
Namespace: `TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel`.
358 lines, width at most100, no sorry, no new attributes or frozen-file edits.
32 source declarations;37 stored constants including five generated auxiliaries.

## Contract and checkpoint4 mapping

- `Blocks S n` is `(Bool→Fin S→Fin n→Bool) ×
  (Fin S→Fin4→Fin(2*n)→Bool) × (Fin S→Fin2→Bool)`.
- `splitTape` partitions the entire `10*S*n+2*S` tape into lengths `2*S*n`,
  `(S*4)*(2*n)`, `S*2`. Its field readers and `_eq` expose all three windows.
- `blocksEquiv` gives a full bijection between this tape and `Blocks`. Its
  key/row/shift readers expose exact getD offsets `(b.toNat*S+v)*n+t`,
  `2*S*n+(4*i+a)*(2*n)+t`, and `10*S*n+2*i+t`.
- `keyRelabel` changes key choice b to b XOR values(v); `rowRelabel` uses a
  supplied Fin4 permutation at each gate; `shiftRelabel` uses existing xorPerm.
- `blockRelabel` combines the three actions. `relabel` conjugates that action
  into a permutation of complete tapes. `relabel_blocks` states the exact
  conjugation identity; the three relabel field equations and getD equations
  state its exact effect on every tape coordinate.
- `relabel_key_fixed`, `relabel_row_fixed`, `relabel_shift_fixed` explicitly
  preserve coordinates with false value masks, fixed row codes, and false
  shift masks, respectively. This covers unused blocks under the caller's
  supplied fixed-point conditions. For one-argument gates, the supplied row
  permutation must fix unused codes2/3; it need not XOR all four codes.
- No probability lemma is added or re-proved. `Edges.lean` demonstrates the
  existing `uprob_comp_equiv (relabel ...)` interface directly.

This completes generic coin-bijection infrastructure, not the full H0=H1
sampler identity. The remaining glue must extend each real assignment
permutation to Fin4 while fixing unused codes; identify masks with wire/argument
values; and prove the concrete seed, garbled-row and view equations. Those
facts are not hidden in assumptions claiming a full sampler identity here.

## Overlap and reuse

- `Asymptotic/Adversary.lean:242,247` blocksEquivX/blocksEquivX_apply and
  :258,262 FunFamily.blocks/blocks_apply are reused directly. The exact readers
  in this module use those published equations, never their definition bodies.
- `Foundations/BitLists.lean:105,110` xorPerm/xorPerm_apply are reused directly
  for shift masks. `keyRelabel` permutes key-choice indices rather than XORing
  stored key bits; its involution uses the existing Bool XOR cancellation
  lemmas and Function.Involutive.toPerm, rather than cloning xorPerm.
- The layout uses Mathlib Fin.appendEquiv, finCongr, finTwoEquiv, prodCongr,
  piCongrRight and arrowCongr. The finite-product index readers are reused.
  The local hb in blocksEquiv_key reads finTwoEquiv.symm's Boolean selector by
  two rfl cases; its nearest definition is Mathlib/Logic/Equiv/Defs.lean:893.
  It is not a new public finite-bit conversion utility.
- The getD readers reuse List.getD_eq_getElem and List.getElem_ofFn. No new
  list-window or ofFn element lemma is introduced. Their interval arithmetic
  is specific to this exact three-region layout.
- SY-5: nearest unmerged source is sc-garble exchange a73072f1,
  Garbling/CoinBlocks.lean:51 pushesUniform_bits_of_blocks, :83
  key_row_blocks_injective and :162 pushesUniform_key_row_blocks. Those give
  uniform restricted key/row marginals for arbitrary selected subsets and
  assignment injections; this module builds a full invertible tape decomposition,
  includes the shift region, and supplies coordinate relabelings. The primitive
  block equivalences are reused from the merged public module, and no probability
  proof is copied. The examined source is preserved verbatim as evidence.
- `NUPPT.coinsCongr`/coinsEquivPoly were searched first. They handle equality
  of total coin polynomials, while this bijection reorganizes all coordinates;
  they do not supply the three-region decomposition.

## Verification

CoinRelabel-10 passes with zero errors. `Edges-01` passes the n=0 shift case,
S=0 inverse case, and public change-of-coins probability interface. Axioms-01
prints all32 source signatures and dynamically enumerates all37 constants
stored in the module (including generated auxiliaries): standard axioms only,
and every transitive closure has sorried=[]. Both diagnostic forms are counted.
All four whole-file seals (A/B by strict/coe), with CLI -DmaxErrors=0, pass.
No Rule10 source repair was needed. The combined seven-file helper subtree
lint is0FAIL/0WARN. Raw logs, source versions, manifests and runners are retained.
The lead still reruns final merged checks. No commits were made by this agent.
