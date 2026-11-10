# Source review for PR #236

PR #236 is open as a draft at `0769cba3e44c56700349f954190fc99d9e622270`,
targeting `cryptography/lwe-sis-constructions` at
`2c37f3f486822a52f4a9e337c6b742e995ebb118`. All foundation modules have
identical bytes at that head and the source review pin
`ec72ed773a690c17ac253707350935cc9e0acb34`. The foundation inventory has 61
declarations, of which 11 have proposed source correspondences. The other
50 cover representation, experiment readers, or the repository's machine
and family interfaces.

I verified the original Pei16 and Wu24 PDF fingerprints and independently
rendered the seven pages used by the returned proposals. The mappings below
are my recommendations for attribution approval. They use the Pei16 PDF
with SHA-256 `1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488`.
Names in the table are under `TCSlib.Cryptography`.

| Declarations | Consumed source | Formal adaptation |
|---|---|---|
| `SIS.Parameters`, `SIS.IsSolution` | Pei16 Definition 4.1.1, PDF p. 20, printed p. 18 | The witness is an integer vector and its nonzeroness is tested before reduction. The natural squared budget replaces the real Euclidean radius. The relation is for a fixed matrix and allows degenerate dimensions. |
| `SIS.successProbability`, `SIS.SISAssumption` | Pei16 Definition 4.1.1, PDF p. 20 | The problem supplies the uniform matrix and success event. Lean gives the finite solver experiment with optional failure, then assumes negligible success for every NUPPT machine on the chosen family. PS10 Definition 26.8 supplies the adversary model context. |
| `LWE.Parameters`, `LWE.Noise` | Pei16 Definitions 4.2.1 and 4.2.3, PDF p. 24, printed p. 22 | Numeric parameters are separate from the noise law. The finite seed map realizes the actual scalar law with its multiplicities. The source permits a general integer error distribution. |
| `LWE.Noise.Bounded` | Pei16 Definition 4.2.1, PDF p. 24 | The every-seed bound is a local restriction for correctness. Wu24 PDF p. 83 supplies a caution about the printed combination of an exact Gaussian with a probability-one support bound. |
| `LWE.noisyValues`, `LWE.sample` | Pei16 Definitions 4.2.1 and 4.2.3, PDF p. 24 | Stack the source's sample vectors as rows to get `A s + e`. The finite product picks a single uniform secret for the batch and independent row errors. Wu24 Definition 20.4, PDF p. 82, gives the equivalent column-matrix presentation. |
| `LWE.decisionAdvantage`, `LWE.DLWEAssumption` | Pei16 Definition 4.2.3, PDF p. 24 | Lean measures an absolute acceptance difference and quantifies over NUPPT machines at the schedule stored in the family. PS10 Definition 26.8 supplies the machine context. A claim for every polynomial sample schedule needs an outer quantifier. |

Use the original Pei16 block identifiers `pdf-1a9802b66031-p020-b001` and
`pdf-1a9802b66031-p024-b001` for the consumed passages. The first landing can
use the corresponding portions of the existing proposed reference with their
coverage stated explicitly. The 11 recommendations are adapted statement
attributions. Keep them out of automatic proof-source insertion. The original
59 candidate records and the worker's partial delivery remain the historical
input to this review.

## Shared registry proposal

I propose registering Pei16 with #236 and handling Wu24 with #237. This uses
the first hunk of the earlier two-entry proposal. I checked the hunk against
both the audited head and current target. The registry's before and proposed
after SHA-256 values are
`7636211fb23c2682c998118f5a954e6fb1c365a9ee9e033c890a8064d8ff5a84` and
`747816a0571be024950d5cbdf48761515d50ffe48dc5232a95f39bc2e8eb4104`.
The registry change is proposed for the user's coordination.

```diff
--- a/blueprint/src/references/sources.json
+++ b/blueprint/src/references/sources.json
@@ -64,6 +64,12 @@
         "switching-lemma"
       ]
     },
+    "Pei16": {
+      "title": "C. Peikert, A Decade of Lattice Cryptography, author version dated 17 February 2016.",
+      "documents": [
+        "peikert2016-lattice-survey"
+      ]
+    },
     "RY20": {
       "title": "A. Rao, A. Yehudayoff, *Communication Complexity and Applications*, Cambridge University Press, 2020.",
       "documents": [
```

## Follow-on source review

The 26 source-related declarations in #237 use the binary hash and pigeonhole
argument in Pei16 PDF pp. 20–21, the Regev encryption and correctness discussion
in Wu24 PDF p. 83, and its ideal hybrid in PDF p. 85. Pei16 PDF p. 24 and Wu24
PDF p. 82 supply the common-secret batch distribution. In particular, the
seedwise encryption identity should cite the encryption formula and the batch
definition. The exact two-advantage bound uses the ideal translation and a
local triangle inequality. The source's scaled rounding and the formal
nearest-codepoint decoder require their respective correctness hypotheses.

Pei16 supplies the integer SIS witness and the bound that rules out trivial
modulus multiples. Wu24 PDF p. 75 also supports the binary hash and compression
argument. Its residue-vector wording is secondary context for the integer
relation. The dyadic profile and explicit probability inequality are local
specializations. Review the returned `same` classifications at the level of
the individual formula or subclaim before attaching a proof citation.

The #238 and #239 inventories contain the remaining 20 and 18 adapter and scalar
arithmetic declarations. Their dispositions are implementation or context items
supported by the existing representation and machine interfaces.

After the user reviews the first mapping and registry proposal, prepare the
scoped reference integration for #236 and verify the final PR head against the
then-current central target. The source review is limited to attribution. The
prior proof audit supplies the Lean proof evidence and the final landing check
still needs to run.

**Not yet clear to merge. The source mappings and shared registry proposal
are ready for review, followed by reference integration and landing checks.**
