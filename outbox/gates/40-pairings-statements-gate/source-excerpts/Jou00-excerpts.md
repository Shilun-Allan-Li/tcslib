# Jou00: excerpts of the passages used (Gate 40)

**Reference.** A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, W. Bosma (ed.), LNCS 1838, pp. 385–393, Springer, 2000 (publisher copy, 9 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `dd423b93a7e2dbeb87e6210b26f4c3ec022c3d0681a0ce72262b1d45c53f6df9` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–4: title
- lines 97–128: §2, p. 387: the Weil and Tate pairings are bilinear and non-degenerate
- lines 129–195: §3, pp. 387–388: the protocol, F_W, the remark e_n(P, P) = 1, two points and F_T, the summary
- lines 325–367: §5, pp. 391–392: security issues

## Lines 1–4: title

```text
          A One Round Protocol for Tripartite
                   Diffie–Hellman

                                    Antoine Joux
```

## Lines 97–128: §2, p. 387: the Weil and Tate pairings are bilinear and non-degenerate

```text

[page break]
                        A One Round Protocol for Tripartite Diffie–Hellman       387

   Using these notions, we can now define the Weil pairing: it is a bilinear
function from the torsion group E[n] to the multiplicative group µn of n-th
roots of unity in some extension of Fp , say Fpk . Given two n-torsion points P
and Q, we compute their pairing en (P, Q) by finding two functions fP and fQ
such that div(fP ) = n(P )−n(O) and div(fQ ) = n(Q)−n(O), and by evaluating:

                            en (P, Q) = fP (Q)/fQ (P ).

    This pairing en : E[n] × E[n] → µn is bilinear and non-degenerate. This
means that en (aP, bQ) = en (P, Q)ab and that for some values of P and Q, we
have en (P, Q) 6= 1. We can easily see that given a point X “independent” from
P and Q, we can reduce the discrete logarithm problem Q = λP on the elliptic
curve to the discrete logarithm problem en (Q, X) = en (P, X)λ in Fpk .
    The variant of the Tate pairing described in [3] is more complicated, since
it operates on divisors instead of points. The Tate pairing operates on n-fold
divisors, i.e. divisors D such that nD is principal, it takes values in µn and it is
bilinear and non-degenerate. Given two n-fold divisors D1 and D2 defined over
an extension Fpk that contains the n-th roots of unity, we find fD1 and fD2 such
that div(fD1 ) = nD1 and div(fD2 ) = nD2 . The Tate pairing of D1 and D2 is
then defined as:
                                                      k
                           tn (D1 , D2 ) = fD1 (D2 )(p −1)/n .
    This pairing is also bilinear and non-degenerate. Moreover, for the purpose
of discrete logarithm reduction, the Tate pairing tn (D1 , D2 ) can easily be trans-
formed into a pairing that involves points. One can simply fix two points R and
S, and remark that tn ((λP ) − (O), (R) − (S)) = tn ((P ) − (O), (R) − (S))λ .
    For more details about the properties and definitions of the Weil and Tate
pairing, we refer the reader to [8,3,4].
```

## Lines 129–195: §3, pp. 387–388: the protocol, F_W, the remark e_n(P, P) = 1, two points and F_T, the summary

```text
3   A Tripartite Diffie–Hellman Protocol

In this section, we want to build an analog of the Diffie–Hellman protocol, that
involves three participants A, B and C, requires a single pass of communica-
tions and allows the construction of a common secret KA,B,C . By a single pass
of communication, we mean that each participant is allowed to talk once and
broadcast some data to the other two. The main idea is as in ordinary Diffie–
Hellman, we start from some elliptic curve E and some point P . Then A, B
and C each chose a random number (a, b or c) and they respectively compute
PA = aP , PB = bP and PC = cP and broadcast these values. Then they respec-
tively compute F (a, PB , PC ), F (b, PA, PC ) and F (c, PA, PB ), where the function
F is chosen in a way that ensures that these numbers will be equal and that
this common value KA,B,C will be hard to compute given PA, PB and PC . The
problem now is to find such an F .
    Using the Weil pairing, it is seems very easy to define such an F using the
following formula:
                            FW (x, P, Q) = en (P, Q)x.

[page break]
388       Antoine Joux

With this definition, one can easily check that:

        FW (a, PB , PC ) = FW (b, PA, PC ) = FW (c, PA, PB ) = FW (1, P, P )abc.

However, this function is not satisfying because en (P, P ) = 1 and thus KA,B,C
is a constant. Nevertheless, the basic idea is quite sound and can in fact be
implemented if we use two independent points P , and Q and if we have the
three participants compute and broadcast (PA , QA), (PB , QB ) and (PC , QC ).
Then A, B and C can respectively compute FW (a, PB , QC ) = FW (a, QB , PC ),
FW (b, PA, QC ) = FW (b, QA , PC ) and FW (c, PA, QB ) = FW (c, QA, PB ). More-
over, all these values are equal and thanks to the independence of P and Q, they
are not constant.
    Moreover, using two points P and Q, it is easy to use the Tate pairing instead
of the Weil pairing, and to define another function F as:

                            FT (x, D1 , D2 ) = tn (D1 , D2 )x .

Then A, B and C can respectively compute:

            FT (a, (PB ) − (QB ), (PC + QC ) − (O)) =
                                  FT (a, (PC ) − (QC ), (PB + QB ) − (O)),
             FT (b, (PA ) − (QA ), (PC + QC ) − (O)) =
                                   FT (b, (PC ) − (QC ), (PA + QA ) − (O)),
             FT (c, (PB ) − (QB ), (PA + QA ) − (O)) =
                                   FT (c, (PA) − (QA ), (PB + QB ) − (O)).

Because of the bilinearity of the pairing, all these numbers are equal and because
of the non-degeneracy, their common value

                         FT (1, (P ) − (Q), (P + Q) − (O))abc

is not independent from the choice of a, b and c.
    Since FT is based on the Tate pairing, it will be faster to evaluate then FW
(see the general remark about the efficiency of the Tate pairing versus that of
the Weil pairing in [4]). Finally, our tripartite Diffie–Hellman protocol can be
summarized as follows:


              Alice                  Bob                Charlie
           Choose a              Choose b              Choose c
      Compute (PA , QA ) Compute (PB , QB ) Compute (PC , QC )
               Broadcast PA , PB , PC and QA , QB , QC .
                      Compute the common key as:
      FT (a, (PB ) − (QB ), (PC + QC ) − (O))
                 FT (b, (PA ) − (QA ), (PC + QC ) − (O))
                             FT (c, (PB ) − (QB ), (PA + QA ) − (O))

[page break]
                       A One Round Protocol for Tripartite Diffie–Hellman     389
```

## Lines 325–367: §5, pp. 391–392: security issues

```text
5     Security Issues

Clearly in order to be secure the tripartite Diffie–Hellman described here requires
the discrete logarithm on the chosen elliptic curve to be hard, and the discrete
logarithm in the finite field Fpk to be hard. Since we placed ourselves in the cases
where either the MOV or the FR reduction applies, the hardness of the elliptic

[page break]
392     Antoine Joux

curve discrete log implies the hardness of the finite field discrete log and we can
remove the second condition. This is a simple restatement of the fact that when
the finite field discrete log, then to solve the elliptic curve discrete log we simply
transport the problem in the finite field using the pairing and then solve the
problem in the finite field. However, it is not known whether the elliptic curve
discrete logarithm on a weak curve is as hard as the discrete logarithm in the
corresponding finite field (in the sense of the MOV or FR reduction). In fact,
this is a very interesting open problem. Moreover, as in the Diffie–Hellman case
this is not the whole story, some Diffie–Hellman like problem and Diffie–Hellman
like decision problem should be hard in order to get security.
     Quite amusingly, we should note that on curves where either the MOV or FR
reduction applies, the usual Diffie–Hellman decision problem is mostly easy. Re-
member that the usual Diffie–Hellman problem is given a quadruple (g, ga , gb , gc)
to decide whether c = ab. This problem can also be expressed with the following
formulation which is slightly different. Given a quadruple (g, ga , h, hb), decide
whether a = b. Now on an elliptic curve where the MOV reduction applies, we
can easily test for a quadruple (P, aP, Q, bQ) whether a = b, it suffices to com-
pute en (aP, Q) and en (P, bQ) and to compare them. This test works as soon
as P and Q are independent (i.e. when en (P, Q) 6= 1). Of course, in the FR
case, such a test also exists. More precisely, one can test for the equality of
tn ((aP ) − (O), (λQ) − (Q)) and tn ((P ) − (O), (λbQ) − (bQ)), where λ is essen-
tially any constant number (some values of λ are excluded, for example λ = 1
is not allowed). Note than when P and Q are not independent, the test usually
doesn’t work, thus some cases of the usual Diffie–Hellman decision problem are
still hard on these elliptic curves.
     With the current knowledge of elliptic curves, we believe that this system
is secure in practice as soon as the discrete logarithm in Fpk is hard. For the
supersingular case (k = 2), we think that p should be a 512 bits prime. In the
trace 2 case (k = 1), we recommend to choose a 1024 bits prime. Moreover,
the usual precautions should be taken, i.e. some large prime q should divide the
order of the elliptic curve, all the points involved in the computation should be
of order q, and we should use the pairing eq or tq .
```
