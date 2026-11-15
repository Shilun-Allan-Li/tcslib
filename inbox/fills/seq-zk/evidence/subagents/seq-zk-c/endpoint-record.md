# EndpointSampling implementation record

Author: seq-zk-c. Assigned by lead after the checkpoint2 closed-evidence manifest was
sealed. This record and all endpoint-* files are future evidence, outside checkpoint
source e978a28274fdeb545e622ae28747221088352512. All72 files in the sealed manifest remain
byte-for-byte unchanged. The lead owns final integration, commits, frozen seals and delivery.

## Supplied interface and coordination

Read root PrefixFolds/PrefixLaws, b PaddedProverSpec/SimulatorMachine, and a
StatisticalRecursion. Coordinated the joint `(verifier tape, prefix)` domain with a and
b before coding. The lead approved generic tape block equivalences, real prefix
identification by the published padded-phase reader, and the optional joint statistical
endpoint convenience theorem. No sibling or main source was edited or checked in its
foreign tree. There is no target change or added cryptographic premise.

The stable new module is EndpointSampling.lean,269lines/max95columns, SHA256
76827a0f531b095aeccd1460ef56ad13bb13612a861f9e7af82bad9069c1c048.

It publishes:
- coinTableEquiv(hlen:m=q*c) and its block reader, for the real prover tape.
- coinBlocksEquiv(v,q,c,hlen:m=v+q*c) and its verifier-take/phase-block readers.
- statClose_reindex, for supplied endpoint equivalences and pointwise endpoint readers.
- PaddedProverSpec.realPrefix_eq_exec, for j<=q and supplied block equalities.
- PaddedProverSpec.realCoinsEquiv, with domain actual `(rho.withV V).ExecCoins` and codomain
  `V.Coins |x| x (Fin q -> pi.P.Coins |x|)`, plus tape/block readers.
- PaddedProverSpec.viewV_eq_realPrefix, the actual encoded real-view endpoint.
- simulate_eq_simPrefix, the typed simulator endpoint from the published raw split reader.
- statClose_view_endpoints, consuming joint real/simPrefix closeness and returning actual
  encoded repeated view versus SQ.simulate with exactly the same error. Its only extra
  readers are p=the original mover count, SQ coinLen=v+q*S.coinLen, and the supplied SQ
  split-tape endpoint; the lead derives them directly from existing readers.

## Search, overlap, reuse, and promotion

Raw exact searches are in endpoint-sampling-searches.log.

- coinTableEquiv is the canonical FunFamily.blocks composed with a finite-length cast.
  The nearest existing assemblies are RepeatedSoundness.accept_le (verifier blocks) and
  GI.gniTapes (graph-specific sampler blocks). Neither exports the required general
  length-cast table equivalence. The block proof directly reuses FunFamily.ofFn_blocks
  and List.ofFn_congr, rather than duplicating the GI.coinSlice_blocksEquiv entrywise proof.
  Promotion request: a named length-cast block equivalence/reader belongs in
  Asymptotic/Adversary.lean if accepted; it is frozen here.
- coinBlocksEquiv directly reuses splitCoins and ofFn_splitCoins_fst/snd from
  Asymptotic/CollectionsHelpers.lean:145ff, then FunFamily.blocks/ofFn_blocks. No sum split,
  take/drop proof, block equivalence, or entrywise window proof was reproduced.
  Its distinct combined codomain is one verifier tape and a finite table of phase tapes.
  Promotion request: combined uniform-tape layout reader in the shared sampling layer.
- statClose_reindex is only published comp_equiv_left/right followed by supplied pointwise
  function equalities. Searches found no combined endpoint-reader interface. It does not
  reproduce probability invariance or a statistical switch. Nearest public declarations
  are StatClose.comp_equiv_left/right (Sampling.lean:179/185). Promotion request to Sampling.
- realPrefix_eq_exec directly composes realPrefix_zero/succ and PaddedProverSpec.padded_phase.
  Its induction is on the number of phase updates, not a duplicated execution/phase proof.
  Nearest real endpoint is b's padded_phase; its single-phase conclusion does not identify
  the finite fold with all phases. The lemma belongs in this topic helper layer.
- realCoinsEquiv and its readers are the typed composition of coinTableEquiv,
  Protocol.withV_vCoinsEquiv/ofFn and product commutation. viewV_eq_realPrefix directly
  combines that interface with Protocol.viewV_withV and the real fold reader.
- simulate_eq_simPrefix directly reuses root simPrefix_eq_phasePrefix and the combined
  block readers; its raw endpoint is supplied by b's exists_phaseSimulator. It contains
  no second simulator recursion or reconstruction of the simulator machine.
- statClose_view_endpoints directly maps joint prefixes to canonical View encoding and
  reuses statClose_reindex plus both endpoint readers. It adds no per-phase statistical
  argument and preserves the error without a triangle/normalization loss.

No frozen source, new simp attribute, foreign-definition unfolding tactic, Lake command,
new iteration host, witness bound, target assumption, or new direct Mathlib root.
CollectionsHelpers was already inside the issued cached TCSlib closure.

## Isolated prerequisites and validation

The lead approved source-copying exact checkpoint helper sources plus b's final canonical
WrappedVerifier/SimulatorMachine public-reader additions, followed by native own checks.
endpoint-prerequisite-sources.json records all source provenance and SHA256s. Own helper
sources were retained. B's two final hashes were verified before copying. No sibling
oleans were copied.

The initial prerequisite Normalization check passed. NormalizationMachine then failed
because the initial209-module own bootstrap lacked ThreeColoring/Machines.olean. This
complete missing-import attempt is preserved, with no source edit to the prerequisite.
Using the lead's explicit existing authorization, APFS-cloned28 missing BASELINE oleans
from root's completed working tree; all source bytes were verified against both own/root
sources and exact checkpoint e978a28274fdeb545e622ae28747221088352512, all olean bytes hashed,
and no existing artifact overwritten. All SequentialZK modules were excluded from seeding.
endpoint-root-baseline-seed.json records each source/artifact hash and path.

Native own-tree checks then passed, one module at a time, in this order:
NormalizationMachine (retry02), PhaseView, WrappedVerifier, RealPhases, PaddedProverSpec,
PrefixFolds, SimulatorMachine, PrefixLaws. Each raw attempt and structured result is retained.

EndpointSampling check01 passed with0errors/0warnings, a fresh own olean,2.45s actual
runtime and maximum resident set size2,236,170,240bytes. The exact attempt source is saved.
Every Lean invocation used LEAN_SLOT_TAG=seq-zk-c, the shared lean-slot wrapper,
/usr/bin/time -l, scripts/lean_check_tree.sh and the separate seq-zk-c olean tree. There was
no interruption, timeout, sampling, or resource exception in this task.

The stable checked source/hash/API were sent to lead and a. No own Lean process remains.

Final reader-compliance amendment: at the lead's request, added full canonical
coinTableEquiv_eq, coinBlocksEquiv_eq, and realCoinsEquiv_eq, each rfl in its home module.
No existing body/reader changed. Check02 passed0diagnostics,2.66s actual runtime,
maxRSS2,237,087,744bytes. Final source/hash sent to lead and a; source remains stable.
