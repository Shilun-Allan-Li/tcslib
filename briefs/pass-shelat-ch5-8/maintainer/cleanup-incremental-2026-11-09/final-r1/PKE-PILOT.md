# Public-key encryption pilot

Design checked against cleanup candidate `7750947a65d262b8a4e4e557b6dae2a48865807a`.
Begin Lean changes after #248 lands on the campaign branch.

## Entry point and ownership

`TCSlib/Cryptography/Encryption/PublicKey.lean` is the exported entry point.
Its contents map names the scheme types, the security games and the three
construction routes. The facade can initially import their existing owners.

| Proposed leaf or retained owner | Source and responsibilities |
|---|---|
| `Encryption/PublicKey/Scheme.lean` | PublicKeyScheme and BitPublicKeyScheme interfaces, their correctness fields, and immediate readers from Asymptotic/PublicKey. |
| `Encryption/PublicKey/EnsembleSecurity.lean` | Single-message and fixed-vector experiments, the bitwise construction, and the single-to-multi-message hybrid. Split the hybrid proof support from Asymptotic/PublicKeyLemmas by its actual consumers. |
| `Encryption/PublicKey/OracleSecurity.lean` | Composability/PublicKey's fixed-length scheme, ciphertext and challenge codecs, two-stage games and IND predicates. Keep the general stateful oracle interfaces in their shared owners. |
| `Encryption/PublicKey/Trapdoor.lean` | Predicate evaluator, trapdoor bit encryption, correctness, security reduction and GL bridge from Asymptotic/PublicKey. Leave the TrapdoorCollection contract in Asymptotic/Collections for its other users. |
| `Candidates/RSA.lean`, `Candidates/Rabin.lean` | Problem experiments and hardness hypotheses, arithmetic implementation, collection and one-way trapdoor results. The PKE map links to the generic trapdoor construction. |
| `Candidates/ElGamal.lean` | For the initial facade, keep the safe-prime DDH experiment and the group scheme together. A later move gives the ElGamal construction its own leaf and the assumption its reusable owner. |
| `Implications/PublicKey.lean` | Proved compositions of explicit assumption sets to multi-message IND-CPA and IND-CCA2 on meaningful message spaces. It imports the required construction and bridge leaves. |

The old Asymptotic/PublicKey and Composability/PublicKey imports can become
compatibility modules with imports of their destination leaves. Consumers
and compatibility modules should use the specific leaves they need. The
facade itself can import the construction routes and stays above them.
Rabin currently imports RSA, and ElGamal uses DiscreteLog and Ensembles.
Keep these imports during the first moves. Move shared arithmetic or
codec owners only after listing all their consumers, including LWE/SIS.

## Construction map

- **RSA.** `RSAAssumption` and `ArithmeticFP` give
  `(rsaTrapdoor H).OneWay` by `rsaTrapdoor_oneWay`. The candidate's
  exact width transport is a prerequisite of the generic GL padding route.
- **Rabin.** `FactoringAssumption`, `ArithmeticFP` and `BlumDensity`
  give `(rabinBlumTrapdoor H).OneWay` by `rabinBlumTrapdoor_oneWay`.
  Its width transport has the same downstream interface and its own
  arithmetic proof.
- **Shared trapdoor route.** A one-way trapdoor collection, hard-core
  predicate and evaluator yield single-bit security by
  `tdpBitScheme_singleBitSecure`. `SingleBitSecure.bitwise` and
  `PublicKeyScheme.Secure.multiMessageSecure` give the existing
  fixed-vector guarantee. The key-visible oracle CPA bridge
  `SingleBitSecure.padded_cpa` is statement-gated with a pending proof.
  Record the multi-message oracle lifting and any CCA2 construction as
  separate proof dependencies.
- **ElGamal.** `ArithmeticFP`, a `SafePrimeGen`, the negligible
  full-length-exception premise, and `DDHAssumption (egGroupGen H G)`
  give `(elGamal H G).Secure` by `elGamal_secure`. Record
  `elGamal_correct` with its admissible-message hypotheses. The
  GroupPKScheme-to-generic-game transport stays a separate proof task.

## First review boundaries

1. Export the facade and verify its import graph and construction map.
2. Move an independent scheme or game cluster with the original
   full names, source statements, docstrings and compatibility imports.
   Verify each affected consumer, actual public types and declaration
   homes, plus foreign reads in the new import context.
3. Continue with the trapdoor construction and ElGamal leaves. Keep
   CCA1 as a documented intermediate. Add an Implications theorem
   after the endpoint and every bridge in its proof have been checked.
4. Update the inherited seal ledger with the original and current
   homes after every move, so the later proof cleanup can use the final
   owner readers.

**Not yet clear to merge — pilot draft; the physical moves follow #248.**
