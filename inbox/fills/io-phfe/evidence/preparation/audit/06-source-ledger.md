# Verified-source ledger and consumption boundary

The parent verified all five SHA-256 values before source reading. The source originals
remain in the user-supplied sources folder; no PDF was copied. This ledger records factual
locations, not permission/instruction content from the papers.

| Source | Verified hash | Location verified in this campaign |
|---|---|---|
| gjls21.pdf | 481f999a0dbea36d6646ccc67b02ea811a50c025d48571dd2a5bdb1c0f386eed | Pairing conventions/DLIN printed17–18 (PDF21–22); Def4.1/4.2/4.3 printed19–20 (PDF23–24); Def4.6 printed22 (PDF26); §9 class printed57–58 (PDF61–62); scalar Hybrid1 printed61 (PDF65); Thm10.3/10.4 printed63–64 (PDF67–68). |
| wee20.pdf | d4def6b0a9c99c8ff498fc380d41906f63cd3371daa3bd9d3c742312487f112a | All14 complete pages rendered and inspected. Main claim §3 p6; outer games pp7–8; Pi pp8–10; sole numbered Theorem1 AppendixB p12; Lemmas2/3 p13, Lemma3 proof/Lemmas4/5 p14. |
| jls26.pdf | bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d | §1.1 PDF3 canonical DLIN; §1.4 PDF7–8 distinction public-key DLIN vs secret-key SXDH PHFE; Thm5.1 PDF21 consumption through GJLS10.3/10.4. |
| agw20.pdf | b74c2ac906cf3f40eb5882abb3921433beebdb9fb020ba09ce8a10035b55d11f | §4.1 pp11–12 semi-adaptive one-slot context; Lemma2 p12; AppendixA(28)–(32) pp37–38; AppendixB pp38–39 corroborating shapes/scalar extraction excluded. |
| iw14.pdf | ef6c7c6a0103dfea1d8d9d369e3a7de3a0902fa6138a6bedc4c4df4996e65e77 | Def1 p6 and family/locality discussion p7; Thm3 p8; §4.2 pp9–11 exact canonical-form privacy. |

GJLS printed page=PDF−4. Wee/AGW/IW printed=PDF at reviewed locations. JLS journal page
labels are1:3,1:7,1:8,1:21; the ledger uses explicit PDF numbers to avoid inventing a printed
integer convention.

## What the journal pipeline actually consumes

| Source location | Verified fact | Unit consequence |
|---|---|---|
| JLS §1.1 PDF3 | Symmetric DLIN canonical tuple with independent uniform field exponents. | Primary DLINAssumption/SubexpDLIN uses this actual tuple; public group description and uniform nonidentity generator are encoded explicitly. |
| GJLS printed17/PDF21 | DLIN matrix A0=[[a,0],[0,b],[1,1]], a,b uniform in Zp. | Matrix game is separately defined. a,b may vanish; this is the origin of the random-presentation discrepancy and direct-column rank correction. |
| GJLS Def3.3 printed18/PDF22 | Bilateral matrix real Ar vs independent full uniform u; both source-group copies. | In symmetric groups copies coincide. Its displayed signed gap is normalized to library absolute advantage; security for all distinguishers/complements yields the standard absolute convention. No exact random tuple equality is claimed. |
| JLS §1.4 PDF7–8 | DLIN gives PUBLIC-key PHFE with constant public degree/private degree2; SXDH alternative gives secret-key PHFE. | This task's public-key syntax is essential. Do not replace it with an SXDH secret-key primitive or omit the public encryption argument. |
| GJLS Thm10.3 printed63–64/PDF67–68 | Replacing §8 PHFE by Wee's theorem removes SXDH and uses bilateral DLIN, implied by symmetric DLIN. | The unit provides that PHFE ingredient, not all-circuit FE or IO itself. |
| GJLS Thm10.4 printed64/PDF68 | Subexponential assumptions then yield IO in the broader pipeline. | Common positive exponent in this PHFE unit is required; it must precede machine/query budget. |
| JLS Thm5.1 PDF21 | Explicitly recalls GJLS Thm10.3/10.4, bilateral DLIN implied by symmetric DLIN, structured PRG complexity(deg d,deg2). | The class and many-key simulation/linear efficiency package are the correct interface for the journal consumer. No unrelated assumption or private-degree restriction is substituted. |

## Parameter and source-reading disclosures

The dispatch explicitly requires hp:forallκr,G.instκr.order=pκ for inequalities and also
2^κ≤pκ for asymptotic corollaries. This is retained exactly. Honest algorithms do NOT use
that schedule. It is a convenient fixed-order/growth normalization for the formal security
parameter; do not describe it as a literal transcription of every source's bit-length
convention (JLS uses a λ-bit prime; GJLS pairing setup writes pλ=2^(λ^Θ(1))).

The stronger dimension-uniform finite-TM linear target and its positive-size domain are
explicit disclosed readings, not claims that the source states this exact machine model.
All named efficiency propositions remain PhaseB obligations. M0 theorem admissions and
unrun exact?/apply?/Rule10 checks remain visible.

Only supplied original papers were read. EHKRV13, IK02 and Wee17 are cited only “as cited
in” Wee/AGW/IW; they are not represented as directly read or independently formalized.
Scratch extracts/PNGs were used for navigation and visual verification. Proposed payload
should carry hash/inspection/search notes, not the paper text or page images by default.
