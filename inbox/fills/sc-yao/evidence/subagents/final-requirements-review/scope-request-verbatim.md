# Recorded scope questions and answers

### ordered-emission.md

Scope request: may the new garbling helper import
`TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines` to reuse its proved
`ColMachines.polyTimeComputable_flatMap_range`? This module is outside the issued order;
reuse avoids re-proving an existing public loop lemma. I would extend the narrowed bootstrap
and roots for this import.

User answer (verbatim): "Approve the extra helper import". Approved 2026-11-15.

Record: `evidence/scope-request/ordered-emission.md`.

### dbl-append.md

A second reuse scope request: may `Yao/HybridProof/DescriptionDecoder.lean` add
`import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine`? Its proved
`MultiMsg.dbl_append` is the exact encoding lemma the decoder needs, but the module is
outside the issued order. This adds no frozen-file edit.

User answer (verbatim): "Approve this helper import". Approved 2026-11-15.

Record: `evidence/scope-request/dbl-append.md`.

### statistical-switch.md

Scope request: may `Yao/HybridProof/StatisticalSwitch.lean` import
`TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas` to reuse
`MultiMsg.abs_uexp_sub_le_uprob`? The brief lists this public interface, but its module is
missing from the supplied order. I’ll extend the narrowed dependency checks for it.

User answer (verbatim): "Approve this probability-helper import". Approved 2026-11-15.

Record: `evidence/scope-request/statistical-switch.md`.

### block-encoding.md

May `Yao/HybridProof/SelectedSlices.lean` import
`TCSlib.Cryptography.Asymptotic.BlockEncryptor`? Its public
`encodeList_eq_flatMap` supplies the challenge-list encoding identity needed by the B1
sampler. The module is outside the issued order; approval lets us reuse it instead of
duplicating its proof.

User answer (verbatim): "Yes". Approved 2026-11-15.

Record: `evidence/scope-request/block-encoding.md`.
