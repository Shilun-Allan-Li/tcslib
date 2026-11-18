# Missing raw PHFE embedding projection: design only

One new PUBLIC reader is proposed: wee20PHFE_raw_embed, the direct function equality
matching the existing setupCore/encCore/keyCore/dec projection-reader style. It exactly
closes the single hEmbed hole in the correctness ladder once natively gated/proved.
The natural-language opening statement is included. No proof or tactic block, native
Lean/lake/Git command, source edit, new runtime definition, efficiency assumption,
E-STMT change, or statement weakening was made.

## Placement and imports

Insert the new reader in owned PHFE/Raw.lean next to the existing core/dec projection
readers, before the PHFE codec namespace if desired. It requires NO new import.
Probes import current Raw plus the permitted core Lean.Elab.Tactic.LibrarySearch only.
At drafting time current Raw has NO wee20PHFE_raw_embed declaration. Run them before
inserting that new reader, or use an isolated checked Raw source prefix excluding it;
otherwise the target itself would contaminate library search. Both probes are anonymous
examples and never import this admitted target fragment. All searches are term exact?%,
so there are ZERO tactic blocks in this invocation. Root-native apply searches/gate
remain required before a new proof.

## Exact dependent types and existing codecs

Let S=wee20PHFE_raw G l n d PG and C=phfeClass l n G.wG d. The proposed reader's
left function has the full dependent type
  (kappa : Nat) -> (pp : PublicParams S.G kappa) ->
    C.Out kappa (S.cprm kappa pp) -> S.DecOut kappa pp.
PHFE.embedValue's corresponding type is
  (kappa : Nat) -> (pp : PublicParams G kappa) ->
    C.Out kappa (PHFE.classParam G l n d kappa pp) -> pp.group.GT.
These are the exact types used by the current raw structure's published projection
readers and its existing codecs, not independently invented output types.

The SECOND probe is an anonymous CODEC-SHAPE diagnostic, NOT a second public-helper
proposal. It spells out the same pointwise embedding with existing codecs:
- raw pp is transported by PHFE.publicParamsEquiv to pp' : PublicParams G kappa;
- raw v has C.Out kappa (S.cprm kappa pp); PHFE.scalarValueEquiv maps that exact value
  to ZMod pp'.group.order;
- its Nat representative is used as the exponent of pp'.group.pair pp'.generator
  pp'.generator. This uses the supplied scalar value; it extracts no group exponent.
The existing publicParamsEquiv_eq/scalarValueEquiv_eq/valueEquiv_eq/embedValue_eq
readers provide its reduction route. No parameter alias is silently re-encoded.

## Output-type boundary honestly disclosed

There is currently NO PHFE.decOutEquiv or wee20PHFE_raw_DecOut reader. The codec-shape
probe's equality therefore checks the current DEFINITIONAL identification of S.DecOut
kappa pp with pp'.group.GT (and the projection target checks the corresponding whole
function type). This is exactly why root-native target typing is needed; this agent
does not claim to have typechecked it. No HEq, opaque axiom, invented cast equality,
or change of decryption codomain is inserted.

If root's target gate succeeds, the primary direct projection is a routine reader and
the codec-shape probe confirms its concrete dependent interpretation using existing
codecs. If a later seal makes output transport inaccessible, a separate dec-output
codec plus equation reader should be proposed/gated then; NONE is added or proved now.
The primary reader remains the minimal interface needed by the current correctness
ladder. The codec diagnostic cannot be mistaken for an already-proved theorem.

## Reuse and axiom status

Existing wee20PHFE_raw_G/cprm/setupCore/encCore/keyCore/dec readers are nearest relatives
and establish the naming/style. PHFE.embedValue_eq is the existing scalar-power formula;
FEScheme.toRaw_embed concerns the efficient/raw projection and cannot substitute for
this concrete raw PHFE projection. No existing theorem with the proposed full name or
concrete raw-embed shape was found. Root already confirmed its absence.

The new reader itself is a logical projection, not an efficient-value construction.
Raw's encMPK/encSK/encCT proof fields remain admitted dependencies until the nine
Encodings obligations are discharged, so this design makes no standard-axiom-only
claim for the final raw correctness root.
