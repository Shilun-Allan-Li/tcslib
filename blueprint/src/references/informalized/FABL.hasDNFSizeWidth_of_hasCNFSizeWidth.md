<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.hasDNFSizeWidth_of_hasCNFSizeWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual DNF representation bounds

**Claim.** If a Boolean function has a CNF with at most \(s\) clauses and a CNF of width at most \(w\), then its Boolean dual has a DNF with at most \(s\) terms and a DNF of width at most \(w\).

**Proof.** Choose a CNF \(\psi\) witnessing the size bound and a CNF \(\psi'\) witnessing the width bound. Switch AND and OR in each formula, producing DNFs. Switching preserves the number of clauses as the number of terms, so the DNF obtained from \(\psi\) has at most \(s\) terms. Switching AND and OR also gives the Boolean dual of the represented function (\(\texttt{FABL.CNFFormula.switchAndOr_toBooleanFunction}\)); therefore the DNF from \(\psi\) computes the dual of \(f\). Apply the same fact to \(\psi'\): its switched formula computes the dual of the function represented by \(\psi'\), which is the dual of \(f\), since \(\psi'\) also represents \(f\). Its term widths are the clause widths of \(\psi'\), so its DNF width is at most \(w\).

**Key facts.** `FABL.CNFFormula.switchAndOr_toBooleanFunction`.
