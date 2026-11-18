/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient
import TCSlib.Cryptography.Encoding.Modular

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stateful simulation interfaces for functional encryption

The simulator receives the public input and the committed functions with their allowed
values. Its state is threaded through encryption and every key query. Algorithms have
explicit finite draws and deterministic cores; the efficient interface additionally carries
the shared uniform sampler-efficiency fields.

## Main definitions

* `FEScheme.Raw.Omega`: the public input and ordered function/value pairs.
* `FEScheme.Raw.Simulator.Raw`: the three stateful raw simulator algorithms.
* `FEScheme.Raw.Simulator`: the raw simulator with uniform efficiency.

## Main results

Every exact simulator algorithm and input encoding has an equation reader.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3 and Remark 4.3; Theorem 9.2 proof,
  Hybrid 1, printed p. 61.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Section 2.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
open TCSlib.Cryptography.CoinSampling

variable {C : FnClass} (S : FEScheme.Raw C)

/-- The simulator's information consists of the public input and the ordered functions
with their values [GJLS21, Definition 4.3, at epsilon one]. Values are supplied before the
scheme's decryption embedding, as in Theorem 9.2's Hybrid 1, printed p. 61. This records
the scalar-value reading, rather than silently replacing the literal target-group values. -/
structure Omega (κ : ℕ) (pp : PublicParams S.G κ) where
  /-- The number of committed function keys. -/
  count : ℕ
  /-- The public input. -/
  publicInput : Fin (C.pubLen.eval κ) → Bool
  /-- The committed functions, in their original order. -/
  functions : Fin count → Fin (C.fnLen.eval κ) → Bool
  /-- Their allowed values on the challenge. -/
  values : Fin count → C.Out κ (S.cprm κ pp)

namespace Omega

variable {S}

/-- The simulator information is encoded by its count, public input, and ordered pairs.
This is encoding glue for the stateful simulator of [GJLS21, Definition 4.3]. -/
def encode {κ : ℕ} {pp : PublicParams S.G κ} (ω : S.Omega κ pp) : List Bool :=
  pairEncode (Candidates.natToList (Nat.size ω.count) ω.count)
    (pairEncode (List.ofFn ω.publicInput)
      ((List.ofFn fun j => pairEncode (List.ofFn (ω.functions j))
        (C.encValue κ (S.cprm κ pp) (ω.values j))).foldr pairEncode []))

/-- The information encoding is the displayed nested pair in commitment order. -/
theorem encode_eq {κ : ℕ} {pp : PublicParams S.G κ} (ω : S.Omega κ pp) :
    ω.encode = pairEncode (Candidates.natToList (Nat.size ω.count) ω.count)
      (pairEncode (List.ofFn ω.publicInput)
        ((List.ofFn fun j => pairEncode (List.ofFn (ω.functions j))
          (C.encValue κ (S.cprm κ pp) (ω.values j))).foldr pairEncode [])) := rfl

end Omega

/-- A raw simulator has stateful setup, ciphertext simulation and key simulation
[GJLS21, Definition 4.3]. Key simulation takes a valid commitment index; its function and
value are already in `Omega`. The index identifies the committed order, which a stateful
simulator can track, and avoids an unspecified out-of-range default. -/
structure Simulator.Raw where
  /-- The simulator's private state. -/
  St : (κ : ℕ) → PublicParams S.G κ → Type
  /-- A canonical encoding of the private state. -/
  encSt : (κ : ℕ) → (pp : PublicParams S.G κ) → St κ pp → List Bool
  /-- Equal state words retain equal states. -/
  encSt_injective : ∀ κ pp, Function.Injective (encSt κ pp)
  /-- The complete setup draw. -/
  SetupDraw : (κ : ℕ) → PublicParams S.G κ → Type
  /-- Setup draws are finite. -/
  [setupFinite : ∀ κ pp, Fintype (SetupDraw κ pp)]
  /-- Setup draws are nonempty. -/
  [setupNonempty : ∀ κ pp, Nonempty (SetupDraw κ pp)]
  /-- Simulated setup returns a public key and private state. -/
  setupCore : (κ : ℕ) → (pp : PublicParams S.G κ) → SetupDraw κ pp → S.MPK κ pp × St κ pp
  /-- The complete ciphertext-simulation draw, depending on its other inputs. -/
  EncDraw : (κ : ℕ) → (pp : PublicParams S.G κ) → St κ pp → S.Omega κ pp → Type
  /-- Ciphertext-simulation draws are finite. -/
  [encFinite : ∀ κ pp st ω, Fintype (EncDraw κ pp st ω)]
  /-- Ciphertext-simulation draws are nonempty. -/
  [encNonempty : ∀ κ pp st ω, Nonempty (EncDraw κ pp st ω)]
  /-- Ciphertext simulation returns the ciphertext and updated private state. -/
  encCore : (κ : ℕ) → (pp : PublicParams S.G κ) → (st : St κ pp) → (ω : S.Omega κ pp) →
    EncDraw κ pp st ω → S.CT κ pp × St κ pp
  /-- The complete draw of one indexed key-simulation query. -/
  KeyDraw : (κ : ℕ) → (pp : PublicParams S.G κ) → St κ pp →
    (ω : S.Omega κ pp) → Fin ω.count → Type
  /-- Key-simulation draws are finite. -/
  [keyFinite : ∀ κ pp st ω j, Fintype (KeyDraw κ pp st ω j)]
  /-- Key-simulation draws are nonempty. -/
  [keyNonempty : ∀ κ pp st ω j, Nonempty (KeyDraw κ pp st ω j)]
  /-- Key simulation returns the functional key and updated private state. -/
  keyCore : (κ : ℕ) → (pp : PublicParams S.G κ) → (st : St κ pp) →
    (ω : S.Omega κ pp) → (j : Fin ω.count) → KeyDraw κ pp st ω j → S.SK κ pp × St κ pp
  /-- Encode a complete setup draw. -/
  encSetupDraw : (κ : ℕ) → (pp : PublicParams S.G κ) → SetupDraw κ pp → List Bool
  /-- Encode a complete ciphertext-simulation draw. -/
  encEncDraw : (κ : ℕ) → (pp : PublicParams S.G κ) → (st : St κ pp) → (ω : S.Omega κ pp) →
    EncDraw κ pp st ω → List Bool
  /-- Encode a complete key-simulation draw. -/
  encKeyDraw : (κ : ℕ) → (pp : PublicParams S.G κ) → (st : St κ pp) →
    (ω : S.Omega κ pp) → (j : Fin ω.count) → KeyDraw κ pp st ω j → List Bool

namespace Simulator.Raw

variable {S}

variable (Sim : Simulator.Raw S)

instance instSetupFinite (κ : ℕ) (pp : PublicParams S.G κ) :
    Fintype (Sim.SetupDraw κ pp) := Sim.setupFinite κ pp

instance instSetupNonempty (κ : ℕ) (pp : PublicParams S.G κ) :
    Nonempty (Sim.SetupDraw κ pp) := Sim.setupNonempty κ pp

instance instEncFinite (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) : Fintype (Sim.EncDraw κ pp st ω) := Sim.encFinite κ pp st ω

instance instEncNonempty (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) : Nonempty (Sim.EncDraw κ pp st ω) := Sim.encNonempty κ pp st ω

instance instKeyFinite (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) (j : Fin ω.count) :
    Fintype (Sim.KeyDraw κ pp st ω j) := Sim.keyFinite κ pp st ω j

instance instKeyNonempty (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) (j : Fin ω.count) :
    Nonempty (Sim.KeyDraw κ pp st ω j) := Sim.keyNonempty κ pp st ω j

/-- One ciphertext-simulation input retains its public parameters, state and information. -/
structure EncInput (κ : ℕ) where
  /-- The public parameters. -/
  pp : PublicParams S.G κ
  /-- The current private state. -/
  state : Sim.St κ pp
  /-- The allowed simulator information. -/
  omega : S.Omega κ pp

/-- One key-simulation input also retains its valid commitment index. -/
structure KeyInput (κ : ℕ) where
  /-- The public parameters. -/
  pp : PublicParams S.G κ
  /-- The current private state. -/
  state : Sim.St κ pp
  /-- The allowed simulator information. -/
  omega : S.Omega κ pp
  /-- The requested function's position in the commitment. -/
  index : Fin omega.count

/-- The ciphertext-simulation word contains pp, the state and the allowed information. -/
def encInputWord (κ : ℕ) (π : Sim.EncInput κ) : List Bool :=
  pairEncode π.pp.encode (pairEncode (Sim.encSt κ π.pp π.state) π.omega.encode)

/-- The ciphertext-simulation input has the displayed nested-pair encoding. -/
theorem encInputWord_eq (κ : ℕ) (π : Sim.EncInput κ) :
    Sim.encInputWord κ π =
      pairEncode π.pp.encode (pairEncode (Sim.encSt κ π.pp π.state) π.omega.encode) := rfl

/-- The key-simulation word additionally encodes the valid query index. -/
def keyInputWord (κ : ℕ) (π : Sim.KeyInput κ) : List Bool :=
  pairEncode π.pp.encode (pairEncode (Sim.encSt κ π.pp π.state)
    (pairEncode π.omega.encode
      (Candidates.natToList (Nat.size π.omega.count) π.index.val)))

/-- The key-simulation input has the displayed nested-pair encoding. -/
theorem keyInputWord_eq (κ : ℕ) (π : Sim.KeyInput κ) :
    Sim.keyInputWord κ π = pairEncode π.pp.encode (pairEncode (Sim.encSt κ π.pp π.state)
      (pairEncode π.omega.encode
        (Candidates.natToList (Nat.size π.omega.count) π.index.val))) := rfl

/-- Simulated setup is its exact complete draw followed by its deterministic core. -/
noncomputable def setup (κ : ℕ) (pp : PublicParams S.G κ) :
    ProbComp (S.MPK κ pp × Sim.St κ pp) :=
  Sim.setupCore κ pp <$> ProbComp.sample (Sim.SetupDraw κ pp)

/-- The simulated setup law is the displayed pushforward. -/
theorem setup_eq (κ : ℕ) (pp : PublicParams S.G κ) : Sim.setup κ pp =
    Sim.setupCore κ pp <$> ProbComp.sample (Sim.SetupDraw κ pp) := rfl

/-- Simulated encryption threads its state through the exact complete draw. -/
noncomputable def enc (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) : ProbComp (S.CT κ pp × Sim.St κ pp) :=
  Sim.encCore κ pp st ω <$> ProbComp.sample (Sim.EncDraw κ pp st ω)

/-- The simulated ciphertext law is the displayed pushforward. -/
theorem enc_eq (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp) (ω : S.Omega κ pp) :
    Sim.enc κ pp st ω =
      Sim.encCore κ pp st ω <$> ProbComp.sample (Sim.EncDraw κ pp st ω) := rfl

/-- Simulated key generation threads its state through the exact indexed draw. -/
noncomputable def key (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) (j : Fin ω.count) : ProbComp (S.SK κ pp × Sim.St κ pp) :=
  Sim.keyCore κ pp st ω j <$> ProbComp.sample (Sim.KeyDraw κ pp st ω j)

/-- The simulated key law is the displayed pushforward. -/
theorem key_eq (κ : ℕ) (pp : PublicParams S.G κ) (st : Sim.St κ pp)
    (ω : S.Omega κ pp) (j : Fin ω.count) : Sim.key κ pp st ω j =
    Sim.keyCore κ pp st ω j <$> ProbComp.sample (Sim.KeyDraw κ pp st ω j) := rfl

end Simulator.Raw

/-- A stateful simulation interface carries uniform efficiency for all three algorithms
[GJLS21, Definition 4.3]. Every witness precedes the security parameter and all inputs. -/
structure Simulator extends Simulator.Raw S where
  /-- Setup sampling and its state/output encoding are uniformly efficient. -/
  setup_eff : SamplesEfficiently
    (fun κ (pp : PublicParams S.G κ) => pp.encode) encSetupDraw
    (fun κ pp (o : S.MPK κ pp × St κ pp) =>
      pairEncode (List.ofFn (S.encMPK κ pp o.1)) (encSt κ pp o.2)) setupCore
  /-- Ciphertext simulation is uniformly efficient with its state and information on input. -/
  enc_eff : SamplesEfficiently toRaw.encInputWord
    (fun κ π => encEncDraw κ π.pp π.state π.omega)
    (fun κ π (o : S.CT κ π.pp × St κ π.pp) =>
      pairEncode (List.ofFn (S.encCT κ π.pp o.1)) (encSt κ π.pp o.2))
    (fun κ π => encCore κ π.pp π.state π.omega)
  /-- Indexed key simulation is uniformly efficient with all other inputs on its word. -/
  key_eff : SamplesEfficiently toRaw.keyInputWord
    (fun κ π => encKeyDraw κ π.pp π.state π.omega π.index)
    (fun κ π (o : S.SK κ π.pp × St κ π.pp) =>
      pairEncode (List.ofFn (S.encSK κ π.pp o.1)) (encSt κ π.pp o.2))
    (fun κ π => keyCore κ π.pp π.state π.omega π.index)

namespace Simulator

variable {S} (Sim : Simulator S)

/-- The raw projection preserves the committed simulator's private-state family. -/
theorem toRaw_St : Sim.toRaw.St = Sim.St := rfl

/-- The raw projection preserves the committed simulator's private-state encoding. -/
theorem toRaw_encSt : Sim.toRaw.encSt = Sim.encSt := rfl

/-- The raw projection preserves the committed simulator's deterministic setup core. -/
theorem toRaw_setupCore : Sim.toRaw.setupCore = Sim.setupCore := rfl

/-- The raw projection preserves the committed simulator's deterministic ciphertext core. -/
theorem toRaw_encCore : Sim.toRaw.encCore = Sim.encCore := rfl

/-- The raw projection preserves the committed simulator's indexed deterministic key core. -/
theorem toRaw_keyCore : Sim.toRaw.keyCore = Sim.keyCore := rfl

end Simulator

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw
