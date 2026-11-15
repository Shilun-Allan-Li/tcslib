# seq-zk-a route assessment

Static review at issue base 107f1e8c218733eac12d6b9bee6fece441271317.
No Lean or Lake execution. No frozen source changed.

The computational/statistical proof route appears mathematically consistent with the issued
statements. This is an assessment, not a checked proof.

## Phase reconstruction

The wrapped verifier needs only the fixed original verifier tape, original auxiliary input,
phase index, and earlier padded prover-message prefix. During real moves, append this local
phase's received real prover messages to that prefix before querying the original cheating
verifier. Verifier filler replies are arbitrary: they are not in the verifier's own received
history and are dropped by the repeated prover at the next phase. The honest prover fillers
are empty and are retained as fixed received-history slots.

The repeated prover uses a fresh block of its tape per phase. Conditional on an earlier real
prefix, the next block remains uniform. Fixing the prefix therefore produces the real view
of the same one-phase wrapped verifier with that prefix in its auxiliary input. Its own tape
can be empty; the original verifier tape is fixed in auxiliary input.

## Normalization

Use a generic capped-slot function on an encoded message list, with exactly p output slots,
where p=proverMoves verifierFirst k. Slot i is the i-th decoded word, default empty, truncated
to B(n) bits. A separate metadata/canonical-encoding validation selects this function or the
all-empty fallback. Appending k-p empty prover fillers gives exactly k slots. This fixes
real phase outputs: their metadata is known, their encoding is canonical, their real count
is p and hB bounds every real prover message independently of verifier behavior.

BinArith.decWords/encWords and the existing map/get/count word hosts cover the decoding and
slot operations. No new private host is needed. A bridge between Strategy.encodeMsgs and
BinArith.encWords should use only both encodings' published nil/cons readers.

## Auxiliary and advice bounds

For a phase auxiliary word

  pairEncode z (pairEncode r (pairEncode (replicate j true) prefixEncoding)),

its length is exactly

  2*|z| + 2*|r| + 2*j + |prefixEncoding| + 6.

The prefix has at most Q(n)*k slots of at most B(n) bits, so its encoding has length at most
Q(n)*k*(2*B(n)+2), including its fixed empty fillers. Since |r|=V'.coinLen n and j<Q(n), a
sufficient polynomial Lz' is

  2*Lz + 2*V'.coins + 2*Q + Q*rounds*(2*B+2) + 6.

The simulator can be selected before Lz: it consumes the full auxiliary z and has strict time
polynomial in n+|z|. Its number of random bits depends only on n: one original-verifier tape
plus Q(n) simulator blocks. Its stored prefix is polynomially bounded on every simulator
tape because normalization caps count and lengths.

For a computational hybrid reduction, the phase index, x, original z, original verifier tape,
and normalized prefix are bounded advice. The witness need not be advice or efficiently
computable. Maximization may range over the finite bounded tuples admitting a witness; only
the tuple is embedded. The suffix simulation and normalization are common postprocessing on
both sides of the one-phase comparison.

## Edge cases

- k=0: there are no received messages even for Q(n)>0; sample the cheating verifier tape and
  produce the exact canonical empty-history view.
- Q(n)=0: the same direct construction, with exact statistical error zero.
- Odd k and either first mover: padding to 2k restores the original phase mover; the count of
  real received prover messages is p, and the padded total is k.
- Malformed/noncanonical simulator output: the validator/fallback and capped-slot operation
  make no shape assumption on simulated views.
- Arbitrary auxiliary length: the statistical premise handles every auxiliary word; the
  computational premise uses the derived Lz'.
- Potential negative delta values: whenever R x y holds, a one-phase StatClose comparison
  implies delta(|x|)>=0 by StatClose.nonneg. Thus Q=0 is harmless and positive-Q summation
  has the expected nonnegative error bound.

## Exact API obstruction

StatZK is a foreign def at ZeroKnowledge/Defs.lean:182 and lacks a published iff reader.
The proposed scope-StatZK-iff.patch supplies the direct statistical analogue of ZK_iff.
It is un-applied and requires the scope approval demanded by the issued brief. No public
existing bridge found in the search constructs StatZK for an arbitrary changed protocol.
