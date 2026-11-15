# Precise statistical hybrid interface for sequential ZK

This is a proof outline and an obligation ledger, not checked composition code. It uses the
checked helper readers and seq-zk-b's approved simulator-fold semantics. No frozen statement
is changed or weakened, and no new computational host is proposed.

## Fixed data and one-phase kernels

Fix an efficient cheating verifier V', an instance x, a witness y with R x y, and original
auxiliary input z. Put n=|x|, k=pi.rounds(n), q=Q(n), b=B(n), and
p=proverMoves pi.verifierFirst k. Thus p<=k. Let W=phaseVerifier V'; its tape is empty and it
is efficient by b's public phaseVerifier_efficient. Obtain S, its uniformity, and hS from the
premise StatZK pi R delta applied to W through the approved StatZK_iff reader.

For a fixed original verifier tape rV, phase j, and earlier padded prover-message prefix pre,
write aux(j,pre)=phaseAux z rV j pre. The raw kernels are:

  realRaw(j,pre)(r) = ((pi.withV W).viewV x y aux(j,pre) r).encode,
  simRaw(j,pre)(s)  = S.simulate x aux(j,pre) s.

The real seed type Rc is the one-phase execution coin type for pi.withV W; the simulated
seed type Sc is S.Coins n. Both are nonempty finite coin types. The witness premise gives
StatClose realRaw simRaw (delta n) for every j and pre, even for a prefix not reachable in
an actual execution, since StatZK holds for every auxiliary word.

The deterministic current-phase update on an arbitrary raw word is

  A(j,pre,raw) = pre ++ normalizePhaseMsgs x aux(j,pre) p b raw ++ replicate (k-p) [].

Map the one-phase closeness through A using public StatClose.map. Every resulting prefix
has exactly k more messages and every new message has at most b bits. In particular, a
simulated raw word need not have valid metadata, a canonical encoding, a valid count, or a
message-length bound: PhaseView enforces all required output invariants on every seed.

## Real normalization is a fixed point

A real one-phase view has metadata x,aux(j,pre), empty wrapper tape, and a received list hist
with exactly p messages. The exact count follows from the public exec_snd_length and
countP_not_moverIsV readers. Its messages all have length at most b by ProverBounded and
R x y; this is independent of the verifier's replies and of the earlier prefix.

Consequently normalizePhaseMsgs_of_encode gives

  normalizePhaseMsgs x aux(j,pre) p b (realRaw(j,pre)(r)) = hist.

The one-phase comparison after A therefore compares the actual real padded-prefix update
pre ++ hist ++ replicate(k-p)[] with the normalized simulated padded-prefix update.
This step uses phaseVerifier_coinLen to identify the wrapper tape with [], the canonical
view reader viewV_withV, and the fixed-point theorem; no foreign definition is unfolded.

This execution-message-bound obligation is now supplied by the checked owned helper
ExecutionBounds.lean: exec_snd_bounded derives it from the uniform pi.P.next length bound,
and exec_snd_slice_bounded covers dropped/taken phase slices. Both use public exec_zero/succ
and core List membership readers; no frozen edit is needed. Their proposed future promotion
is beside exec in Interaction.lean. The count readers are already public in the owned module.

## Common hybrid seed space

Let RV be V'.Coins n and D=Rc*Sc. Use one common finite nonempty global seed type

  Omega = RV * (Fin q -> D).

The table contains both real and simulator coins at every phase, so unused coins are ignored.
For hybrid H_i, fold the phases j in range q from pre=[], using the real A-update when j<i
and the simulated A-update otherwise, with the table's corresponding Rc or Sc component.
Output View.encode <x,z,List.ofFn rv,finalPrefix>. Thus H_0 is all simulated and H_q is all
real. The folds are mathematical uses of the existing List.foldl/loop semantics; they do not
introduce a new machine host.

Each raw one-phase comparison can be put on D on both sides by public uniform projections:
first precompose its real side with pushesUniform_fst, then precompose its simulated side
with pushesUniform_snd by symmetry. The exact second step is

  (h.comp_pushesUniform pushesUniform_fst).symm
    .comp_pushesUniform pushesUniform_snd
    .symm

with types inferred for D=Rc*Sc. The result compares r |-> realRaw(r.1) and
r |-> simRaw(r.2) on the same current-phase seed. Nonempty ignored coin spaces justify the
public projection facts. Nearest readers: HardcoreBit/Basic.lean:207,210 and
Asymptotic/Sampling.lean:202,157.

## One adjacent comparison

Fix i<q and split the full coin table into first i entries, current entry i, and its q-i-1
tail. This is a bijection, assembled from standard Fin/function table equivalences. The
shared seed a contains rv and the first i entries, and determines the same real prefix pre_i
in H_i and H_(i+1). Let K_a(nextPrefix,tail) run only simulated updates for phases i+1,...,q-1
and then produce the canonical final view with rv. Both hybrids use this same K_a.

For each a, the current real/simulated A-updates are delta(n)-close as above. Apply the public
randomized-suffix reader, directly rather than adding a duplicate theorem:

  (statClose_iff _ _ _).2 fun T =>
    hCurrent.abs_uprob_sub_le_prod (fun next tail => T (K_a next tail)).

This yields the conditional comparison including the independent simulator suffix. Apply
statClose_average to average over a. Its nonnegative error premise is obtained from any
one-phase hS comparison by StatClose.nonneg using R x y. Reindex both sides along the same
coin-table splitting bijection using comp_equiv_left/right. The result is exactly

  StatClose H_i H_(i+1) (delta n)

on the common Omega seed space. This is a product-coordinate argument; no conditional
probability on a zero-probability event is needed.

## Full chain and endpoints

Apply statClose_chain H q (delta n) to the adjacent comparisons. It yields
StatClose H_0 H_q ((q:Real)*delta n); symmetry gives the required real/simulated order.
The q=0 case is reflexivity at error zero and needs no sign premise on delta.

The all-simulated endpoint is exactly b's approved phasePrefix semantics:

  phasePrefix S k B vF x z rV rS 0 = [],
  prefix_(j+1) = prefix_j ++ normalizePhaseMsgs x (phaseAux z rV j prefix_j) p b
      (S.runAtL n (pairEncode x (phaseAux z rV j prefix_j))
        (coinBlock (S.coinLen n) j rS)) ++ replicate(k-p)[].

Use phasePrefix_succ_simulate and the published block readers to identify each typed S seed.
b's exists_phaseSimulator interface provides a uniform S_Q with coins CV+Q*S.coins, one
fixed rV=take CV, rS=drop CV, and canonical output View.encode<x,z,rV,prefix_q>.
FunFamily.blocks/ofFn_blocks and the standard coin-splitting equivalences identify this
with H_0; the unused Rc coordinates preserve laws through public uniform projections.

The all-real endpoint requires the following exact execution reader in the owned source.
If pre_j is V's received-prover prefix after 2*k*j moves against the repeated prover, then
its received prefix after 2*k*(j+1) moves is

  pre_j ++ onePhaseReceived(pi.P,phaseVerifier V',aux(j,pre_j),proverCoinBlock_j)
    ++ replicate(k-p)[].

Prove this by induction on the k real moves using the move-index readers and
phaseVerifier_next_phaseAux, then count the honest prover's empty filler moves. Verifier
filler replies are arbitrary and are dropped at the next phase; only prover fillers are
fixed to []. This cheating-verifier reader is not supplied directly by the honest-only
seqRep_exec_phase theorem. It is an explicit remaining endpoint obligation, not an assumed
lemma. The normalized-real fixed point above then identifies H_q with the full repeated
real view. Coin equivalences turn the Rc table (with unique empty wrapper tapes) into the
repeated prover tape. Remove unused Sc seeds via uniform projections.

These endpoint law identifications plus the chain give exactly q*delta(n), with no extra
normalization/fallback error. For k=0 every prefix update is empty and both endpoints are
the exact empty-history view; the semantic normalization also handles this case directly.
No efficient honest prover is required, since only its output-message bound is used.

## Computational continuation

For ZK, the same phase comparison must use polynomially bounded auxiliary/advice and an
efficient suffix map. b's current phasePrefix endpoint proof uses the registered loopState'
host. A suffix initialized with an arbitrary bounded pre and phase offset should be derived
from that same host, not a private loop. This is useful to expose publicly when convenient;
the statistical argument itself needs only the deterministic suffix function and its coins.
