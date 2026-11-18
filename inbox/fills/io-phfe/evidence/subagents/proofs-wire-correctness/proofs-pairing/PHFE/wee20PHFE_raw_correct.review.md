# Raw PHFE correctness: one-hole candidate

Exact live frozen opening prose/header preserved. One outer tactic block; ONE named
local hole hEmbed, precisely the missing raw embed projection reader confirmed by root.
No new helper proof, definition, import, sampler, machine, efficiency hypothesis, or
source edit. No Lean/lake/Git command was run. Native validation remains pending.

## Existing all-outcomes / typed-core route

correct_iff and honestRun_eq expose the actual sequential honest experiment. Published
setup_eq/enc_eq/keyGen_eq and OracleComp.map_eq_bind/bind_assoc/pure_bind turn its
pushforwards into the existing four-bind sequence: pp, setup draw a, encryption draw s,
key draw t, then pure HonestOutcome. AllOutputs.bind plus allOutputs_true proves the
claim on every draw without a custom sampler or support theorem. allOutputs_pure then
reduces only the outcome's structure projections.

Existing raw core/cprm projection readers and PHFE core readers expose the typed
quadratic algorithms. PHFE.keyCore_eq retains the ORIGINAL function word, so decryption
uses its exact decode; no encode/decode normalization of aliases occurs.
The substantive pointwise identity is the proved Quadratic.quadratic_dec_eq at those
decoded inputs and duplicated private vector. PHFE.class_eval_eq and embedValue_eq
identify its value with the permitted class scalar embedded in the target group.
Quadratic.scheme_raw_correct is the already-proved bundle corollary of the same typed
law; using quadratic_dec_eq directly fits the explicit PHFE cores and avoids a second
raw-bundle transport. No correctness/probability law is reproved.

## Precisely isolated missing-reader hole

hEmbed states only:
  (wee20PHFE_raw G l n d PG).embed = PHFE.embedValue G l n d
It does NOT assume the desired decryption or all-outcomes correctness identity.
Raw.lean currently publishes G/cprm/setupCore/encCore/keyCore/dec readers but no embed
reader and no raw-bundle equation reader. Root has confirmed this and authorized a
separate later target/probe for wee20PHFE_raw_embed. This draft does not fill that
reader by unfolding the raw definition.

The function equality is dependently typed: raw embed accepts
  (kappa : Nat) -> (pp : PublicParams raw.G kappa) ->
  C.Out kappa (raw.cprm kappa pp) -> raw.DecOut kappa pp,
whereas PHFE.embedValue accepts PublicParams G kappa, C.Out kappa(classParam ... pp),
and returns pp.group.GT. With current readers/default elaboration those projection
types are definitionally the intended ones. If a seal blocks them, the appropriate
next design target is a public DecOut/raw-value transport codec or typed reader,
NOT an efficiency assumption or an altered correctness statement. No such helper is
proved/added here. hEmbed is the only term sorry.

## Axiom status caveat required by the raw record

No standard-axiom-only claim is made. Even after this local reader is supplied, the
wee20PHFE_raw structure contains encMPK/encSK/encCT injectivity proof fields whose
PHFE.Encodings theorems remain admitted. They may occur transitively in projection
reader constants until those raw-record obligations are proved. The current proof
draft must be reviewed under that dependency state, not advertised as a closed root.
No mathematical obstruction was found beyond the missing reader interface.
