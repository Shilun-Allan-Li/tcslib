# Shared hHybridResample: one-block ladder

Scratch only; native check pending. No Lean, lake, build, Git, live edit, public helper,
sampler or machine was used. This is NOT a completed proof. The101-line fragment has one
outer tactic block and one explicit inner admission, hRead, described precisely below.

## Sole remaining hole

hRead is only the actual-game/read/conditional-matrix equality. It asserts that acceptance
of the actual hybrid with threshold j+(if real then1 else0) is its same pp,M,S,U and D-coins
average, read through obs with selected scalar column

- `Matrix.mulVec M (fun a => S a j)` for real=true;
- `fun a => U a j` for real=false.

Fill it by the published accept/probability/bind/pure readers and local hybrid/obs
expansion. The scalar matrix equality is pointwise: at b=j the real branch takes M*S and
the random branch takes U; at b<j both use M*S; at b>j both use U. The real selected entry
is the matrix multiplication entry read as a row dot the selected S-column, using
Matrix.mul_apply' (or a permitted core/Mathlib show/rfl reduction), never an exponent
witness. Bool cases and natural-number inequalities settle the guards. hRead contains no
resampling claim, no uniform transport, no rank assumption and no additional loss.

## Substantive resampling already drafted around that hole

The local cols(m) is the existing Equiv.piComm: a scalar mask matrix is viewed as a tuple
of WHOLE columns. hIgnore proves that changing either mask's selected column leaves obs
unchanged for every fixed externally supplied selected response. It compares scalar
response matrices under the actual encoding/probability function; it does not read an
algorithm by unfolding it. Earlier columns alone can use S, later columns alone U, and
the selected output is the supplied vector. Matrix.mul_apply and finite-sum congruence
read those coordinates; no counting fact is reproved.

hRealColumn invokes the existing ProbComp.expect_sample_coord with β=Fin2→K, using
hIgnore to discharge its residual-coordinate independence premise. hRandomColumn invokes
the SAME API with β=Finℓ→K. The equivalence is transported explicitly on each side by
expect_sample_equiv; the fresh-vector/sample-matrix order is exchanged once with
expect_sample_comm. The two calls reuse the public law; its update/fiber-counting proof
is not duplicated. Each hF follows directly from Function.update_of_ne and
Fin.ne_iff_vne applied to the *column* index.

A small hResample performs the Bool dispatch. True commutes S/U on both sides to expose
hRealColumn; false exposes hRandomColumn directly. Finally the same two scoped Fubini
commutations put M after S and U, matching the original ideal/idealCore exactly. Every
S/U matrix entry remains drawn; the selected fresh vector is exactly uniform on its
whole type; the original D.Coins average remains inside obs throughout. No zero-dimension
exception is introduced: the outer j:Fin(d.evalκ) already handles d=0 by an empty domain,
and the random column law permits Finℓ empty when ℓ=0.

## Actual static reuse searches this invocation

- Read live shared SelfReduction:455-590; parent reports its hReductionTransport now
  native PASS, and the whole live file has890 lines before wrapping one old long line.
- `rg -n 'def piComm|theorem piComm_apply|def transposeAddEquiv|transposeAddEquiv_apply|transpose_apply|mulVec.*apply'`
  over Mathlib Logic/Equiv and matrix directories. Read Matrix/Basic:790-812 and
  Logic/Equiv/Basic:150-168. Selected Equiv.piComm:158 (pure coordinate swap), avoiding
  an unnecessary additive-algebra equivalence. Its constructors/core projections may
  reduce under the permitted exact/rfl steps; no core/Mathlib definition is in a simp list.
- Read Probability:378-392: exact expect_sample_coord(j,F,hF) signature. Its generic β is
  precisely what permits whole-column planting. This public theorem already derives the
  law from expect_sample_update; no local resampling/independence theorem is reproved.
- `rg -n '^theorem (mulVec_eq|mul_apply|update_apply|update_same)|^.*update_noteq|^.*update_of_ne|^.*transpose_apply'`
  over Matrix/Mul, Function/Basic. A guessed Data/Matrix/Defs path did not exist; actual
  matrix definitions live in LinearAlgebra/Matrix/Defs. Matrix.mul_apply is Mul:293,
  mul_apply' is299; Function.update_of_ne is Function/Basic:494.
- `rg -n '(ne_of_val_ne|val_ne_of_ne|ne_iff_vne|val_ne_iff|val_injective)'` over Data/Fin;
  Fin.ne_iff_vne:90 gives exactly the val-non-equality-to-index-non-equality transport.
- Read Function/Basic:486-502 to verify update_of_ne's argument order `(h,v,f)`.

Only proof-local obs/ideal/idealCore definitions are passed to dsimp. The probability
itself is always retained as the public ProbComp.prob constant; equality under its
arguments is transported by congrArg, without foreign ProbComp.prob definitional closure.

## Native-check notes / line budget

All fresh work is one outer proof block using ?_/swap local ladders. There is exactly
one term-sorry, hRead. Root should check this surrounding ladder before filling hRead.
The hRealColumn/hRandomColumn final steps use explicit sample-equivalence term chains,
rather than a generic reverse-equivalence simp that might fail to see a local type alias.
The final sample commutations are scoped to their explicit matrix expectation levels.

Fragment:101 lines, maximum92 columns. Replacing the sole one-line hHybridResample body
in the890-line live source gives990 lines (991 after the pending old width wrap), before
filling hRead. Removing the fragment's two explanatory code comments frees2 lines if
needed. If hRead's final normalization exceeds the remaining room, parent should record
that exact size pressure and move technical scalar transport into an appropriate
cycle-free theorem module, rather than duplicate any generic resampling machinery.
No native typecheck, seal pass or standard-only chain is claimed for this candidate.
