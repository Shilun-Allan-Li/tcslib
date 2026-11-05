/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Message authentication codes, signatures and collision-resistant hashing (definitions)

The definitions of [PS10] ch. 5 (prong A of the ch. 5–8 campaign), stated as games of the `Games`
framework.

**Adversaries.** Forgers and collision finders are machines (`Complexity.NUPPT`), run as framework
computations by the machine decoder (`NUPPT.toComp`, `NUPPT.toCompOn`) with the bit-string codec
(`bitCodec`). The oracle is logged (`QueryImpl.withLog`), so "`A` did not query `m`" is read from
the log.

**Deviations, declared once here.**
- **Fixed lengths.** Messages at parameter `n` are `ℓ(n)`-bit strings (the source's message space
  `{M_n}`), and tags and signatures are `t(n)`-bit strings. An algorithm's output is read at its
  length by `padFin`. The oracle codec needs fixed lengths.
- **Algorithms.** `Gen`, `Tag` and `Sign` are uniform machines (PPTs), as in the ch. 2–4 layer's
  `PrivateKeyScheme`. `Ver` is a polynomial-time function, read as accepting on output `[true]`.
  Correctness holds for every coin string: the probability-one reading of the source.
- **Query budgets.** A forger's number of oracle queries is an explicit polynomial `q`, universally
  quantified in the security definitions, as in the ch. 2–4 layer's `OracleEnsemble.Indist`. The
  one-time notions fix the budget to one.
- **Signature forgers receive the public key.** The experiment displayed in Def 136.2 writes
  `A^{Sign_sk}(1^n)`; `Ver` is public, so the forger gets `pk` (the standard definition).

## Main definitions

* `Authentication.MAC`, `MAC.forgeGame`, `MAC.Secure`: [PS10, Defs 134.1, 134.2].
* `Authentication.SignatureScheme`, `SignatureScheme.forgeGame`, `SignatureScheme.Secure`,
  `SignatureScheme.OneTimeSecure`: [PS10, Defs 135.1, 136.2, and the one-time notion after
  Def 136.2].
* `Authentication.CRH`, `CRH.Compresses`, `CRH.collisionGame`, `CRH.CollisionResistant`:
  [PS10, Def 140.1].

## Main results

None yet: the theorems on these notions (Thms 135.4, 137.2, 142.3, 144.1) are stated in the
statement phase of prong A, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.2–§5.5 (book pp. 133–142).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The first `a` and the last `b` bits of an `(a + b)`-bit string. -/
def splitBits {a b : ℕ} (w : Fin (a + b) → Bool) : (Fin a → Bool) × (Fin b → Bool) :=
  (fun i => w (Fin.castAdd b i), fun j => w (Fin.natAdd a j))

/-- The parameter-tagged input `⟨1^n, w⟩` of a deterministic polynomial-time algorithm. -/
def atParam (n : ℕ) (w : List Bool) : List Bool := pairEncode (List.replicate n true) w

/-! ### Message authentication codes -/

/-- A **message authentication code** over `ℓ(n)`-bit messages with `t(n)`-bit tags
[PS10, Definition 134.1]: a key generator `Gen(1^n)`, a tagging algorithm `Tag_k(m)` (activated on
`⟨k, m⟩`, its output read as `t(n)` bits), and a deterministic polynomial-time `Ver` on
`⟨1^n, ⟨k, ⟨m, σ⟩⟩⟩`, with perfect correctness. -/
structure MAC where
  /-- The message length `ℓ(n)`. -/
  msgLen : PolyExpr
  /-- The tag length `t(n)`. -/
  tagLen : PolyExpr
  /-- The key generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The tagging algorithm `Tag_k(m)`. -/
  tag : NUPPT
  /-- The verification algorithm; `[true]` is "accept". -/
  ver : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Tag` is a PPT. -/
  tag_uniform : tag.Uniform
  /-- `Ver` is deterministic polynomial-time. -/
  ver_poly : PolyTimeComputable ver
  /-- Perfect correctness, for every coin string [PS10, Definition 134.1 (4)]. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (rt : tag.Coins n),
    ver (atParam n (pairEncode (gen.runAt n [] rg) (pairEncode (List.ofFn m)
      (List.ofFn (padFin (tagLen.eval n) (tag.runAt n (pairEncode (gen.runAt n [] rg)
        (List.ofFn m)) rt)))))) = [true]

namespace MAC

variable (M : MAC)

/-- `Ver_k(m, σ)` accepts. -/
def Accepts (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Prop :=
  M.ver (atParam n (pairEncode k (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true]

instance (n : ℕ) (k : List Bool) (m : Fin (M.msgLen.eval n) → Bool)
    (σ : Fin (M.tagLen.eval n) → Bool) : Decidable (M.Accepts n k m σ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one tagging oracle at parameter `n`. -/
abbrev oracleSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n)

/-- The **tagging oracle** `Tag_k(·)`: each query `m` is answered by `Tag_k(m)` with fresh coins. -/
noncomputable def tagImpl (n : ℕ) (k : List Bool) : QueryImpl (M.oracleSpec n) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (M.tag.Coins n)).bind fun rt =>
    .pure (padFin (M.tagLen.eval n) (M.tag.runAt n (pairEncode k (List.ofFn m)) rt))

/-- The codec of forgers: one oracle, and a final output of `ℓ(n) + t(n)` bits read as `(m, σ)`. -/
def forgerCodec (n : ℕ) :
    MachineCodec (M.oracleSpec n) (Fin (M.msgLen.eval n + M.tagLen.eval n) → Bool) :=
  bitCodec (fun _ => M.msgLen.eval n) (fun _ => M.tagLen.eval n) (M.msgLen.eval n + M.tagLen.eval n)

/-- **The MAC forgery game** [PS10, Definition 134.2] at parameter `n`, for the forger `A` with
query budget `b`: sample a key `k ← Gen(1^n)` and `A`'s coins, run `A` against the logged tagging
oracle, and win when `A`'s output `(m, σ)` is accepted and `m` was not queried. -/
noncomputable def forgeGame (A : NUPPT) (b n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (M.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (M.tagImpl n (M.gen.runAt n [] rg)).withLog (A.toComp (M.forgerCodec n) n b r)
      ((), [])).bind fun res =>
    .pure (decide (M.Accepts n (M.gen.runAt n [] rg) (splitBits res.1).1 (splitBits res.1).2 ∧
      ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))

/-- **A secure MAC** [PS10, Definition 134.2]: for every non-uniform PPT forger and every
polynomial query budget, the forgery probability is negligible. -/
def Secure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, accept (M.forgeGame A (q.eval n) n) ≤ ε n

end MAC

/-! ### Digital signatures -/

/-- A **digital signature scheme** over `ℓ(n)`-bit messages with `t(n)`-bit signatures
[PS10, Definition 135.1]: `Gen(1^n)` outputs `⟨pk, sk⟩`, `Sign_sk(m)` is activated on `⟨sk, m⟩`,
and a deterministic polynomial-time `Ver` on `⟨1^n, ⟨pk, ⟨m, σ⟩⟩⟩`, with perfect correctness. -/
structure SignatureScheme where
  /-- The message length `ℓ(n)`. -/
  msgLen : PolyExpr
  /-- The signature length `t(n)`. -/
  sigLen : PolyExpr
  /-- The key generator `Gen(1^n)`, with output `⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The signing algorithm `Sign_sk(m)`. -/
  sign : NUPPT
  /-- The verification algorithm; `[true]` is "accept". -/
  ver : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Sign` is a PPT. -/
  sign_uniform : sign.Uniform
  /-- `Ver` is deterministic polynomial-time. -/
  ver_poly : PolyTimeComputable ver
  /-- Perfect correctness, for every coin string [PS10, Definition 135.1]. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (rs : sign.Coins n),
    ver (atParam n (pairEncode (pairFstD (gen.runAt n [] rg)) (pairEncode (List.ofFn m)
      (List.ofFn (padFin (sigLen.eval n) (sign.runAt n (pairEncode (pairSndD (gen.runAt n [] rg))
        (List.ofFn m)) rs)))))) = [true]

namespace SignatureScheme

variable (S : SignatureScheme)

/-- `Ver_pk(m, σ)` accepts. -/
def Accepts (n : ℕ) (pk : List Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (σ : Fin (S.sigLen.eval n) → Bool) : Prop :=
  S.ver (atParam n (pairEncode pk (pairEncode (List.ofFn m) (List.ofFn σ)))) = [true]

instance (n : ℕ) (pk : List Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (σ : Fin (S.sigLen.eval n) → Bool) : Decidable (S.Accepts n pk m σ) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one signing oracle at parameter `n`. -/
abbrev oracleSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n)

/-- The **signing oracle** `Sign_sk(·)`: each query `m` is answered by `Sign_sk(m)` with fresh
coins. -/
noncomputable def signImpl (n : ℕ) (sk : List Bool) : QueryImpl (S.oracleSpec n) Unit unifSpec :=
  QueryImpl.ofComp fun _ m => (ProbComp.sample (S.sign.Coins n)).bind fun rs =>
    .pure (padFin (S.sigLen.eval n) (S.sign.runAt n (pairEncode sk (List.ofFn m)) rs))

/-- The codec of forgers: one oracle, and a final output of `ℓ(n) + t(n)` bits read as `(m, σ)`. -/
def forgerCodec (n : ℕ) :
    MachineCodec (S.oracleSpec n) (Fin (S.msgLen.eval n + S.sigLen.eval n) → Bool) :=
  bitCodec (fun _ => S.msgLen.eval n) (fun _ => S.sigLen.eval n) (S.msgLen.eval n + S.sigLen.eval n)

/-- **The signature forgery game** [PS10, Definition 136.2] at parameter `n`, for the forger `A`
with query budget `b`: sample `⟨pk, sk⟩ ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the
logged signing oracle, and win when `A`'s output `(m, σ)` is accepted under `pk` and `m` was not
queried. -/
noncomputable def forgeGame (A : NUPPT) (b n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.signImpl n (pairSndD (S.gen.runAt n [] rg))).withLog
      (A.toCompOn (S.forgerCodec n) n b (pairFstD (S.gen.runAt n [] rg)) r) ((), [])).bind
    fun res =>
    .pure (decide
      (S.Accepts n (pairFstD (S.gen.runAt n [] rg)) (splitBits res.1).1 (splitBits res.1).2 ∧
        ∀ e ∈ res.2.2, e.2.1 ≠ (splitBits res.1).1))

/-- **A secure signature scheme** [PS10, Definition 136.2]: for every non-uniform PPT forger and
every polynomial query budget, the forgery probability is negligible. -/
def Secure : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, accept (S.forgeGame A (q.eval n) n) ≤ ε n

/-- **A one-time secure signature scheme** [PS10, the notion after Definition 136.2]: Def 136.2
for forgers that may query the signing oracle once. -/
def OneTimeSecure : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, accept (S.forgeGame A 1 n) ≤ ε n

end SignatureScheme

/-! ### Collision-resistant hashing -/

/-- A **family of collision-resistant hash functions**, in its syntax [PS10, Definition 140.1]:
an index generator `Gen(1^n)`; for each index `i`, a domain `D_i` of `d(n)`-bit strings and a
range `R_i` of `r(n)`-bit strings, given by membership tests; and a deterministic polynomial-time
evaluation `h_i(x)` on `⟨1^n, ⟨i, x⟩⟩`. The source's remaining clauses are properties a
construction is proved to have: compression `|R_i| < |D_i|` (`CRH.Compresses`) and collision
resistance (`CRH.CollisionResistant`).

**Deviation:** domains and ranges are sets of fixed-length strings, given by membership tests,
for the source's index-dependent `h_i : D_i → R_i`. The tests are needed: in Construction 142.2
the exponents range over `Z_{p−1}`, and an `n`-bit exponent domain would contain the trivial
collisions `x`, `x + (p − 1)`. -/
structure CRH where
  /-- The domain length `d(n)`. -/
  domLen : PolyExpr
  /-- The range length `r(n)`. -/
  rangeLen : PolyExpr
  /-- The index generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The evaluation `⟨1^n, ⟨i, x⟩⟩ ↦ h_i(x)`. -/
  eval : List Bool → List Bool
  /-- Membership in the domain `D_i`. -/
  inDom : ∀ n, List Bool → (Fin (domLen.eval n) → Bool) → Bool
  /-- Membership in the range `R_i`. -/
  inRange : ∀ n, List Bool → (Fin (rangeLen.eval n) → Bool) → Bool
  /-- `Gen` is a PPT ("ease of sampling"). -/
  gen_uniform : gen.Uniform
  /-- Evaluation is polynomial-time ("ease of evaluation"). -/
  eval_poly : PolyTimeComputable eval

namespace CRH

variable (H : CRH)

/-- `h_i(x)` as an `r(n)`-bit string. -/
def hash (n : ℕ) (i : List Bool) (x : Fin (H.domLen.eval n) → Bool) :
    Fin (H.rangeLen.eval n) → Bool :=
  padFin (H.rangeLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn x))))

/-- **Compression** [PS10, Definition 140.1, "compression"]: from some parameter on, at every
generated index `i`, `h_i` maps `D_i` into `R_i` and `|R_i| < |D_i|`.

**Deviation:** from a threshold on, since the ch. 2–4 instance generators are degenerate below
one (their deviation D10). -/
def Compresses : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ rg : H.gen.Coins n,
    (∀ x, H.inDom n (H.gen.runAt n [] rg) x = true →
      H.inRange n (H.gen.runAt n [] rg) (H.hash n (H.gen.runAt n [] rg) x) = true) ∧
    Fintype.card {y // H.inRange n (H.gen.runAt n [] rg) y = true} <
      Fintype.card {x // H.inDom n (H.gen.runAt n [] rg) x = true}

/-- **The collision game** [PS10, Definition 140.1] at parameter `n`, for the machine `A`: sample
`i ← Gen(1^n)` and `A`'s coins, run `A(1^n, i)`, read its output as `(x, x')`, and win when
`x, x' ∈ D_i`, `x ≠ x'` and `h_i(x) = h_i(x')`. -/
noncomputable def collisionGame (A : NUPPT) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (H.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
    let i := H.gen.runAt n [] rg
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (A.runAt n i r))
    .pure (decide (H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2))

/-- **Collision resistance** [PS10, Definition 140.1]: for every non-uniform PPT `A`, the collision
probability is negligible. -/
def CollisionResistant : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, accept (H.collisionGame A n) ≤ ε n

end CRH

end TCSlib.Cryptography.Authentication
