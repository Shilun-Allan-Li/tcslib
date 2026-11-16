# Dispatch · Gate 43

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/14e681e6cfe2e70fb5248fbf2938a024290b061d/outbox/gates/43-gsw-fills-gate)
is staged on the exchange (pushed).
Seyoon dispatches.

Gate 42 is reserved for sc-yao. The phase-6 plan's provisional gate numbers 42 and 43 will be renumbered later.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 43 (GSW fills, lattice campaign
phase 5) in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 14e681e6cfe2e70fb5248fbf2938a024290b061d.
   Read outbox/gates/43-gsw-fills-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit together draft PR #339 (gsw-core) at Lean head
   839f36cca9b4af0570c014f03f19858d0a03cbfb and draft PR #338 (gsw-security)
   at Lean head d45d3682089cb6fd04f4d075f48a464fefaa143c, with campaign
   records 4ed91289d6132f71ace06b3d9fd87539956d6a88, using the pack. This is a
   proof audit of the 35 frozen GSW targets whose statements Gate 41
   accepted. Audit each proof for soundness on the routes Gate 41 validated,
   in particular: Encrypts.mul with its exact |x1|*b2 term; encrypts_chain;
   decrypt_of_encrypts, including odd q and q = 2, 3;
   decrypt_of_encrypts_dyadic; eval_encrypts via runWith_rel; the condition
   of decrypt_keygen_eval; F7's bijection; F5's column hybrid; and F6's four
   hybrids with the 2*N*eps term. Check that every frozen statement and its
   prose is unchanged. Check duplication: an undisclosed duplicate of a
   public lemma is a major. Grade the reviewers' findings GC-01 to GC-06 and
   GS-01 to GS-06. GS-01 is pending Seyoon's ruling as ledger debt with
   promotion P-1. GS-02 is the erratum of missed relatives; grade its
   distAdv_comp item on its own. Also check Rule 10 (the seal evidence and
   the GC-05 matcher note), the docstring and sketch rules, the sources rule
   (no fabricated tags; check the citations against the DW-7 transcriptions
   in the bundle), and evidence completeness, under the rulings and
   dispositions in the pack. #338 and #339 change disjoint files and merge in
   either order, and each was built on the tip separately. A combined build
   of both is a merge condition the maintainer runs, not an audit item.
3. Return gate43-gsw-fills-findings.md as Markdown in this chat, with
   findings marked by PR. If you need multiple evidence files, return a ZIP
   containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `4ed91289`, then this dispatch commit) and the exchange commit `14e681e6` (on the exchange tip
`641d7af7`) are pushed.

**Ready to dispatch**
