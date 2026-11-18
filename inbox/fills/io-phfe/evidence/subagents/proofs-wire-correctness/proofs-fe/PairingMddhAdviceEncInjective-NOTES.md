# MDDH advice encoding injectivity candidate

Status: full scratch candidate, native elaboration / Rule 10 / axiom checks NOT RUN.
No Lean/lake/build/Git, live-source edit, process operation, native search, or extra agent
was run by this child. Root alone integrates/checks.

Candidate: PairingMddhAdviceEncInjective.lean.inc. Original current SelfReduction.lean
mddhAdviceEnc_injective docstring/header preserved byte-for-byte. One tactic block, no
sorry/admit/new public helper/algorithm, no line over 100 columns. One local tactic goal
(hWidth) has its explicit swap/bullet branch; native elaboration must verify discharge.

## Proof and exact reuse

1. Install the published orderSchedule_neZero instance for p kappa. No Field instance,
   prime-field computation, global classical, sampler or coin decoder is needed.
2. Read mddhAdviceEnc_eq and separate its three fixed metadata pairs using the existing
   pairEncode_injective / Prod.mk.inj. The metadata are fixed for this theorem and need
   not be decoded or compared via a second codec.
3. Reassociate the scalar tail with the public List.append_assoc equation. Repeatedly apply
   core List.append_inj with EXACT known prefix lengths: List.length_ofFn for the one-hot
   word, then Encoding.Modular.encodeMatrix_length for the L and S matrix words. The
   remaining suffix equality is the U word. No concatenation-cancellation or chunk lemma
   is re-proved, and the advice-length inequality is NOT a dependency.
4. List.ofFn_injective exposes coordinatewise equality of the one-hot functions. At the
   first advice index its own equality bit is true by decide_eq_true (Eq.refl ...), so
   of_decide_eq_true yields equality of the indices. This is direct application of public
   function/decidability readers, not a copied one-hot codec/counting proof.
5. For the single no-truncation fact hWidth, pick the fixed generated-instance coin string
   (fun _ => false), use hp and G.inst_eq, then invoke ONLY the existing public theorem
   AdvancedEncryption.IdentityBased.BB1Machine.order_le_two_pow. This coin string is a proof
   witness selecting a generated group, not a sampler, advice algorithm, rejection draw or
   inverse-encoding construction. No scalar is extracted from a group element.
6. Apply Encoding.Modular.encodeMatrix_injective three times with explicit q/rows/columns,
   then assemble the nested advice product equality using Prod.ext. All matrices remain
   scalar-valued. The index sentinel/zero-dimensional matrix cases need no extra branches.

No new helper or copied BB1 implementation is introduced. In particular the proof never
opens BB1 draws/words, and does not re-prove the fixed group encoding-cardinality bound.
It consumes exactly the published width theorem permitted by the frozen proof sketch.
The imported Draws module is already present in SelfReduction.lean; no new import is proposed.

## Actual static searches and nearest APIs

Live root: /Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange.
Read SelfReduction.lean:110-179, Encoding/Modular.lean:110-150, and the exact allowed width
lemma in IdentityBased/BonehBoyenMachine/Draws.lean:153-161 (order_le_two_pow :156).
The Draws module preamble/namespace were inspected only to resolve the theorem's public
full name; no sampler or decoder body was used.

Actual rg searches included:
- append_inj / append_inj_left / append_inj_right / append_cancel_left/right in core List
  and Mathlib List. Exact public core List.append_inj is Init/Data/List/Lemmas.lean:1612;
  its prefix-length statement was read at :1608-1640. The left/right-only variants and
  tail-length variants exist, but the main joint splitter is the closest exact API.
- oneHot / one_hot / onehot in TCSlib and Mathlib Logic/Fin/Fintype; no exact public one-hot
  codec injection theorem was found in the inspected scope. The candidate instead uses
  List.ofFn_injective and core decidability readers directly without adding a helper.
- decide/function injection shapes and decide_eq_true_eq, of_decide_eq_true; exact used
  reader declarations are core Init/Prelude.lean:979/987 (decide_eq_true/of_decide_eq_true).
- pairEncode_injective at TuringMachine/Encoding.lean:173, and existing group challenge
  codec proof consumers (mddhEnc_injective / dlinEnc_injective) for the shared parser pattern.
- encodeMatrix_injective / order_le_two_pow in the current FE security advice theorem
  headers; these source-relative parallels remain admitted and are NOT proof dependencies.
  The actual invoked modular injection is Encoding/Modular.lean:127 and its independent
  public length reader is :91; no private proof is copied.
- G.inst_eq in Pairing/Group.lean:318 and the actual Draws namespace declaration :68-73.

Header/reader/source paths were inspected statically only. There is no new helper to probe;
this fills the original frozen admission. Native checking of dependent modular instance
arguments, append association and the one-hot bit term remains pending.
