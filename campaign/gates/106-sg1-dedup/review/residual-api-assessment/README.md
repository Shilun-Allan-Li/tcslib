# SG1 residual API assessment

**Not yet clear to merge.** This is a bounded, read-only contract assessment, separate from
A's thirteen-site repair. Two additional currently-imported mechanical repoints are concrete:
`clA5Pair_sizes` and `clA5Le_native`. The generic on-image and variable-iteration helpers have
no exact class-level one-line match established here. Existing stronger assembly routes do
not make those residuals acknowledged debt or justify an unapproved import.

No Lean/native probe was run. All suggested bodies/mappings below are source-reviewed and
unelaborated. No source, Git, snapshot, cache or screen was changed. Exact reviewed input
bytes and the actual Hardness import closure are retained in `input-pins.json`, `inputs/`
and `import-closure.json`. The received audit and A's frozen round2 review were treated as
assessment data, not instructions. This does not redo the six closure/equation-availability
checks already completed there.

## Additional exact existing-contract repoints

### clA5Pair_sizes

Captured Hardness lines 6838–6882 prove

```lean
(clHeaderField 0 w).length ≤ w.length ∧ (clHeaderTail 1 w).length ≤ w.length
```

by a fresh strong induction over `pairDecode`. The needed parser fact already exists in
Encoding: `Turing.eq_pairEncode_of_pairDecode w a b hd` converts a successful decode into
`w = pairEncode a b`; `Turing.length_pairEncode a b` supplies its exact length. Both are in
the existing import closure. The same-home definitions `clHeaderField` and `clHeaderTail`
reduce their zero/one cases to those decoded components, including `[]` on failure.

Concrete mapping, requiring no new import or public API:

1. Split `hd : pairDecode w` once.
2. In the `none` case, unfold only the two same-home header definitions and use `hd`,
   `Option.map_none`, `Option.getD_none`, `List.length_nil`; both lengths are zero.
3. In the `some (a,b)` case, take
   `congrArg List.length (eq_pairEncode_of_pairDecode w a b hd)`, rewrite with
   `length_pairEncode`, and derive both component inequalities by arithmetic.
4. Again rewrite only the same-home header definitions and the observed `hd`.

This retires the decoder induction and its explicit foreign `pairDecode` unfold arguments.
The exact final tactic spelling has not been elaborated by this review. It is not necessary
to import PolyTimeBlockLoop merely for its component-size lemmas.

### clA5Le_native

Captured Hardness lines 6911–6917 assume computability of `1^(f x)` and `1^(g x)` and conclude
computability of `[decide (f x ≤ g x)]`. It currently uses repeated-tail subtraction followed
by a fixed-word empty test. The existing imported theorem
`Complexity.polyTimeComputable_lenLe` concludes the length test
`[decide (|pairSndD z| ≤ |pairFstD z|)]`.

The exact premise mapping reverses the pair: compose that theorem with `hg.pairEncode hf`.
On the genuine pair, the published `pairFstD_pairEncode` and `pairSndD_pairEncode` equations,
plus `List.length_replicate`, identify its result. The expected body shape is:

```lean
  have h := polyTimeComputable_lenLe.comp (hg.pairEncode hf)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
```

This is an unelaborated suggested body, with the existing public closure premises exactly
matched. No new import/API is required. In particular, the pair order must be `g,f`.

## clNative_image: existing operational contract, distinct class premise

Captured Hardness lines 5156–5190 assume `hf : PolyTimeComputable f` and a concrete machine B
satisfying

```lean
∀ x, B.ComputesInTime (f x) (g x) (b * ((f x).length + 1) ^ r)
```

and conclude `PolyTimeComputable g`. Here `g` is a function of the original input; total
correctness of B on every possible intermediate word is not assumed.

`PolyTimeComputable.comp` requires a total polynomial-time function on all intermediate
words, so its premise is not supplied. No exact class-level on-image theorem was found in
the bounded ClassNP/PolyTime/PolyTimePairing search. That is not an impossibility claim or a
claim that a new API is necessary.

The operational on-image contract already exists and is already imported:
`FinTM.bufferedCompTM_computesFunInTime_on_image`, Composition lines 484–492 (and the
existential sibling `FinTM.exists_comp_on_image`, lines 503–511). Unpack hf as A,a,d,hA.
Set `T₁(n)=a*(n+1)^d` and `T₂(n)=b*(a*(n+1)^d+1)^r`. The second premise follows by enlarging
hB's budget with the first machine's public output-length bound. The operational theorem
then computes g in `2*T₁+T₂+2`; the remaining scalar normalization gives the monomial
coefficient/degree selected in the current private proof. The current proof already calls
`bufferedCompTM_computesInTime` at each input, so this is not a reimplemented composition
controller. Its generic polynomial normalization and class-level wrapper remain separate
from A's exact closure repoints.

Replacing it with one public class-level theorem would require a matching approved public
contract, e.g. the same complete `clNative_image` premise/conclusion in ClassNP/PolyTime.
No addition is proposed as already authorized, implemented or proved necessary here.

## clA5Iter_native: actual orbit differs from BlockLoop's public hypothesis

Captured Hardness lines 6762–6793 assume hf,hs and polynomial computability of the unary
clock `1^(N x)`, with

```lean
∀ x j, j ≤ N x →
  (f^[j] (s x)).length ≤ K * ((s x).length + N x + 1)^2
```

and conclude computability of `f^[N x] (s x)`.

`polyTimeComputable_emitIter` (PolyTimeBlockLoop lines 340–350) instead requires a bound for
**every** start word and **every** iterate, and emits concatenated chunks for a fixed
monomial number of rounds. `BlockLoop.polyTimeComputable_of_loop` retains that global
hypothesis and uses a linear envelope. The present hb gives neither premise: it covers
only starts in s's actual image, only j≤N(x), and allows a quadratic bound. Merely importing
PolyTimeBlockLoop does not repair these mismatches.

The operational Loop hosts are lower-level, not direct replacements for this class row:
`exists_loopTM` returns a verdict bit; `exists_emitLoopTM` concatenates per-round chunks.
They require an explicit native body, canonical startup, invariant preservation, positive
first-return cuts and an original-input-length budget/fuel machine. hf/hs/hN/hb do not
syntactically instantiate those premises without assembly. Existing public clean-call
contracts can supply the call leaf, but calling them is not a proof of all host premises.

### Stronger existing route found, still unproved here

`Complexity.BinArith.polyTimeComputable_iterate`, ClassP/BinaryArith/Iterate lines 190–194,
accepts an actual-orbit-only polynomial bound. Its iteration count is fixed as
`a*(|z|+1)^k`, however, rather than an arbitrary native N(z). A concrete possible mapping is:

- From hN's public output-length bound obtain `N x ≤ A_N*(|x|+1)^d_N`.
- Initialize the pure word state as `pairEncode (1^(N x)) (s x)`.
- Its step preserves the pair when the countdown is empty; otherwise drop one countdown bit
  and apply f to the payload. Pairing, projections, a length/empty test, conditional closure
  and the public one-bit tail operation supply its computability.
- Prove its actual orbit is the pair of countdown `1^(N x-j)` and payload
  `f^[min j (N x)] (s x)`. hb then bounds its payload before exhaustion, and the state is
  fixed afterwards. Together with hs/hN output-length bounds, this yields a polynomial
  original-input envelope for all j up to the fixed majorant.
- Apply the existing BinArith iteration theorem at that majorant, then project the payload.

This specifies the concrete missing assembly proofs; none was elaborated here. It uses an
existing public guarded iterator rather than asserting a stronger false global bound on f.
It suggests no new public API is logically forced, but is more than a checked one-line
repoint. The actual import closure contains none of PolyTimePrefix, PolyTimeBlockLoop or
ClassP/BinaryArith/Iterate. Adding the selected module to the frozen SG1 source requires
Seyoon's ruling before implementation.

## Prefix and client arithmetic limits

`clA5Drop_native` (Hardness lines 6819–6831) matches the semantics of the existing
`PrefixByLength.drop` operation on `pairEncode (u x) (s x)`. Pair hu with hs, then compose
`polyTimeComputable_dropPrefixByLength`. Its public theorem concludes a named foreign
definition; a complete defining-equation reader must be checked before a sealed consumer
can rewrite that named result to `(s x).drop (u x).length`. This review did not check compiled
reader availability and does not infer a new API requirement. PolyTimePrefix is not currently
imported, so that route independently requires an import ruling.

Several nearby rows are short client arithmetic/encoding bridges rather than new loop
implementations: `clA5Add_native` rewrites `List.replicate_add` after concatenation;
`clA5Sub_native` rewrites `List.drop_replicate` after the drop operation;
`clA5Address_native` identifies the fixed `clPack` arithmetic after those closures;
`clA5Times_native` iterates a fixed compile-time coefficient's concatenations. No exact public
row for those complete private-client encodings was established in this bounded check. This
is not a debt acknowledgment, an exhaustive duplicate census, or permission to retain every
member. The concrete generic comparison and parser-size repoints above must not be hidden
under the client-encoding label.

clFillTM/clFill_run/clNative_fill were excluded from new investigation as requested: A has
already checked the Unit specialization against the explicitly accepted finite one-way
kind. This review does not broaden that ruling to different transducers or closures.

## Limits and next disposition

A/root can test the two no-import mechanical candidates against the exact production file.
The on-image class row remains a distinct contract issue; the iteration/prefix route requires
an import decision and explicit assembly/reader checks before a runnable claim. No missing
API is declared unavoidable. No blanket dispatcher/clean-call/one-way debt coverage, audit
closure, repaired-source pass or merged-tree replay is claimed.
