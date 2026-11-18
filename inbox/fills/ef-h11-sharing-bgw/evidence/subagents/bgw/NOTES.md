# bgw sub-agent notes: TCSlib/Cryptography/MPC/BGW/Efficient.lean

File: /home/user/work/wt-bgw/TCSlib/Cryptography/MPC/BGW/Efficient.lean, 236 lines, max width 100.
Last logs (after re-mirroring lead's updated ShamirEfficient, md5 in lead-md5.txt):
  06-SecretSharing_Efficient.log rc=0, 07-SecretSharing_ShamirEfficient.log rc=0 (5 sorry lines, lead's),
  08-MPC_BGW_Efficient.log rc=0, 0 errors, 0 warnings, 0 sorry. Peak RSS ~2.87 GB.
style_lint.py: 0 findings.

## Public declarations (namespace TCSlib.MPC.BGW)
- shamirResharer (def): Shamir re-sharing over ZMod π.p with explicit coins ρ; Resharer (ZMod π.p) (π.k-1).
- shamirResharer_reshare (reader, rfl).
- shareRaw_shamirResharer: shareRaw ⟨π.encode,⟨resWord x,⟨bits (ρ i x), resWord (label j)⟩⟩⟩ = resWord (reshare i x j).
- polyTimeComputable_reshare: ∃ f poly-time with that spec (f = shareRaw).
- reshare_dealerSamples (b): bundle of the above with DealerSamples (dealerSamples_shamir b) — coins of a re-sharing, in the encoding the machine reads, are one dealer draw.
- resWord_bgwEval_input / resWord_bgwEval_const: input/const gates, identity step.
- addModW_bgwEval: addModW ⟨p,⟨a_j,b_j⟩⟩ = resWord (bgwEval (a.add b) j).
- mulModW_bgwEval_smul: mulModW ⟨p,⟨c,a_j⟩⟩ = resWord (bgwEval (a.smul c) j).
- mulModW_bgwEval_mul: mulModW ⟨p,⟨a_j,b_j⟩⟩ = resWord ((bgwEval a * bgwEval b) j).
- recombineRaw_reshare: recombineRaw ⟨p, encWords [⟨label i, R.reshare i (u i) j⟩ : i ∈ l]⟩ = resWord (recombine A fun i => R.reshare i (u i) j), l nodup listing A.
- recombineRaw_shareRaw: composition of the two with shamirResharer (list entries are shareRaw outputs).

## Reader census (foreign defs → readers used)
- Shamir.scheme → scheme_share; Shamir.isSharing_share (lemma).
- Shamir.shareRaw → shareRaw_spec, polyTimeComputable_shareRaw.
- Shamir.recombineRaw → recombineRaw_spec. (polyTimeComputable_recombineRaw cited in docstrings only.)
- Shamir.addModW/mulModW → addModW_resWord, mulModW_resWord (poly-time lemmas cited in docstrings).
- Shamir.resWord, coinEquiv, ShamirParams.encode, shamirAdm, DealerSamples: opaque in statements only; dealerSamples_shamir used as a term.
- BGW.bgwEval → bgwEval_input/const/add/smul (bgwEval_mul NOT used; see missing reader).
- Resharer.reshare / isSharing_reshare: structure projections.
- Mathlib: Pi.add_apply, Pi.mul_apply, List.mem_toFinset, Finset.ext (lemmas).
- MISSING reader: degreeReduce_apply : degreeReduce R A u j = recombine A fun i => R.reshare i (u i) j
  (beside Protocol.lean:77). No route through published lemmas: degreeReduce is only read by
  isSharing_degreeReduce (an IsSharing statement, not a pointwise value).

## Duplication searches (grep -rn over TCSlib/**/*.lean, excluding my file)
Resharer 6 (Protocol, Privacy); bgwEval 44 (Protocol, Privacy); degreeReduce 8 (Protocol);
reshare 10 (Protocol); resWord 40, recombineRaw 4, shareRaw 4 (ShamirEfficient only);
Mathlib Resharer|degreeReduce 0.
Near-relatives: Privacy.lean:73 dealtInputs (dealer-produced input share vectors, abstract coins;
shamirResharer is its per-value counterpart for re-sharing with Fin-coins); Privacy.lean:58
bgwEval_congr_of_isLinear (per-party gate locality, value-level). No restatement found.

## Statement changes vs targets
- No new step-map defs: the step maps are id (input/const), addModW, mulModW, shareRaw,
  recombineRaw, all with the lead's readers/poly-time lemmas; defining aliases would duplicate.
- Added recombineRaw_shareRaw (composition) — extra.
- Dealer-coins glue stated as a bundle (∃ f, poly ∧ spec ∧ DealerSamples) to avoid a bare restatement of dealerSamples_shamir.
