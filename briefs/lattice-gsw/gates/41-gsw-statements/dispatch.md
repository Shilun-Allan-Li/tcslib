# Dispatch · Gate 41

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/c72de14a98d2ad107600323b171985017465e33a/outbox/gates/41-gsw-statements-gate)
is staged on the exchange (local commit on branch `stage/gate41-exchange`, chained on the Gate 40 exchange commit
`870bed6c`, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 41 (GSW statements, lattice campaign
phase 5) in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at c72de14a98d2ad107600323b171985017465e33a.
   Read outbox/gates/41-gsw-statements-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit together draft PR #332 at Lean head 94eae71b779c4ca0f76c138d699f4d737dbd6cee
   (DAGCircuit depth readers and runWith_rel) and draft PR #333 at Lean head
   48d796a8a68cd50897047f01825a8132dd19e8d8 (GSW, stacked on #332), with campaign
   records 86d19094aafecc1e19d208c6629b179cfdd14009, using the pack. This is a
   statement audit under rulings Q1-Q16 (Q9 changed) and QS1-QS2. Check the
   fidelity of the gadget presentation to GSW13, AP14 3.2 and Pei16 6.1.3, with
   the differences disclosed, using the source excerpts in the pack. Check the
   truth of every one of the 35 target statements, with particular attention
   to the noise bounds: the asymmetric Encrypts.mul bound N*b1 + |x1|*b2, the
   chain bound b0 + k*N*b, the depth bound (N+1)^depth*b and the leveled
   correctness condition 2*(l*((N+1)^L*m*B)) < floor(q/2); flag any off-by-one
   or missing hypothesis. Check IND-CPA (two DLWE advantages plus 2*N*eps from
   the column leftover-hash lemma), the reuse of the existing LWE, Regev and
   Lossy.gadget layer and the disclosed columnHashParameters duplicate (Q11),
   the #332 additions (the readers, and runWith_rel and getD_lt_depth audited
   as proofs), Rule 10, docstrings and sketches, and whether phase 5 fits the
   phase-6/7 roadmap (BV14, ruled Q12). The add/add conflict with #331 in the
   shared AdvancedEncryption facade and the rebuilds listed under Merge
   interaction are merge conditions the maintainer runs, not audit items.
3. Return gate41-gsw-statements-findings.md as Markdown in this chat, with
   findings marked by PR. If you need multiple evidence files, return a ZIP
   containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pins `356321ac` and `86d19094`, the two dispatch commits) and the exchange commits `870bed6c` and
`c72de14a` (on the exchange tip `da8f8f66`) must be pushed first.

## For Seyoon (rulings; the gate can be dispatched as is)

- **Q14 ingest.** Ruling Q14 (A) put the GSW13 ingest (`blueprint/src/references/`) in the phase-5 statement PR; #333
  has none. (A, rec.) Defer it as for the pairings (Q12): text excerpts in the gate now, the ingest from transcriptions
  of the passages used later; (B) add it to #333 before merge (the PDF needs your go-ahead); (C) a separate records
  ingest PR now.
- **Pei16 coverage.** The GSW docstrings cite Pei16 §5.4.3 and §6.1.2–§6.1.3, present only in the raw extraction.
  (A, rec.) Extend the approved scoped excerpt `peikert2016-lattice-survey.md` with those passages at the ingest;
  (B) leave the raw extraction as the citation target.

**Ready to dispatch**
