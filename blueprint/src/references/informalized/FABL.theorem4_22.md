<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.theorem4_22 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Concentration for Width-Bounded DNF

**Claim.** A Boolean function represented by a DNF of width at most $w$ has Fourier spectrum concentrated through degree $30w$ times the specified switching depth, with error at most $\varepsilon$.

**Proof.** Split according to whether $w=0$. In that case, choose a representing DNF. Its width is exactly zero, so its Boolean function is constant: the zero-width constancy result says its values at any two inputs agree (\texttt{DNFFormula.toBooleanFunction\_eq\_of\_width\_eq\_zero}). A constant function has no Fourier weight above degree zero, and therefore is concentrated up to degree zero with any nonnegative error (\texttt{isFourierSpectrumConcentratedUpTo\_zero\_of\_constant}). This gives the desired bound when $w=0$. If $w>0$, apply the positive-width concentration theorem, which gives concentration through the stated degree cutoff with error $\varepsilon$ (\texttt{theorem4\_22\_of\_pos}).

**Key facts.** `FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`, `FABL.isFourierSpectrumConcentratedUpTo_zero_of_constant`, `FABL.theorem4_22_of_pos`.
