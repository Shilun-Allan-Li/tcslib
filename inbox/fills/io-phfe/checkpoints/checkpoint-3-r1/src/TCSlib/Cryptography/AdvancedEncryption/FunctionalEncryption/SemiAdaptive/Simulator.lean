/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator
import TCSlib.Cryptography.CoinSampling.Contract

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stateful semi-adaptive simulation

The simulator generates a public key before the challenge. Its ciphertext algorithm
receives only the public input. Each subsequent key algorithm receives the public
input, queried function and allowed scalar value, threading one private state.
Every exact algorithm is a core applied to one finite complete draw.

## Main definitions

* `FEScheme.Raw.SASimulator.Raw`: the three explicit raw simulation algorithms.
* `FEScheme.Raw.SASimulator`: their uniform sampler-efficiency interface.

## Main results

Algorithm and layout readers expose the exact stateful laws without unfolding.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; ePrint 2020/1420, §2.2, p.5.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, §4.1, pp.11–12.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games
open TCSlib.Cryptography.CoinSampling

variable {C : FnClass} (S : FEScheme.Raw C)

/-- A raw semi-adaptive simulator has stateful setup, public-input-only ciphertext
simulation, and key simulation from each allowed scalar. [Wee20, §2.2, p.5]. Its private
state has one polynomial bit width, uniform over all public parameters. -/
structure SASimulator.Raw where
  /-- The private state bit width, uniform over all public parameters. -/
  stLen : PolyExpr
  /-- The simulator state over the drawn public parameters. -/
  St : (kappa : ℕ) → PublicParams S.G kappa → Type
  /-- The canonical fixed-width state word used by uniform efficiency. -/
  encSt : (kappa : ℕ) → (pp : PublicParams S.G kappa) → St kappa pp →
    Fin (stLen.eval kappa) → Bool
  /-- State encodings lose no information. -/
  encSt_injective : ∀ kappa pp, Function.Injective (encSt kappa pp)
  /-- The complete setup draw. -/
  SetupDraw : (kappa : ℕ) → PublicParams S.G kappa → Type
  /-- Setup draws are finite. -/
  [setupFinite : ∀ kappa pp, Fintype (SetupDraw kappa pp)]
  /-- Setup draws are nonempty. -/
  [setupNonempty : ∀ kappa pp, Nonempty (SetupDraw kappa pp)]
  /-- Setup generates the simulated public key and initial private state. -/
  setupCore : (kappa : ℕ) → (pp : PublicParams S.G kappa) → SetupDraw kappa pp →
    S.MPK kappa pp × St kappa pp
  /-- The complete ciphertext draw depends on the state and public input only. -/
  EncDraw : (kappa : ℕ) → (pp : PublicParams S.G kappa) → St kappa pp →
    (Fin (C.pubLen.eval kappa) → Bool) → Type
  /-- Ciphertext draws are finite. -/
  [encFinite : ∀ kappa pp st x, Fintype (EncDraw kappa pp st x)]
  /-- Ciphertext draws are nonempty. -/
  [encNonempty : ∀ kappa pp st x, Nonempty (EncDraw kappa pp st x)]
  /-- Ciphertext simulation never receives the private challenge input. -/
  encCore : (kappa : ℕ) → (pp : PublicParams S.G kappa) → (st : St kappa pp) →
    (x : Fin (C.pubLen.eval kappa) → Bool) → EncDraw kappa pp st x →
    S.CT kappa pp × St kappa pp
  /-- One key's complete draw depends on its state, public input, function and value. -/
  KeyDraw : (kappa : ℕ) → (pp : PublicParams S.G kappa) → St kappa pp →
    (Fin (C.pubLen.eval kappa) → Bool) → (Fin (C.fnLen.eval kappa) → Bool) →
    C.Out kappa (S.cprm kappa pp) → Type
  /-- Key-simulation draws are finite. -/
  [keyFinite : ∀ kappa pp st x f mu, Fintype (KeyDraw kappa pp st x f mu)]
  /-- Key-simulation draws are nonempty. -/
  [keyNonempty : ∀ kappa pp st x f mu, Nonempty (KeyDraw kappa pp st x f mu)]
  /-- Key simulation receives exactly the public input, function and allowed scalar. -/
  keyCore : (kappa : ℕ) → (pp : PublicParams S.G kappa) → (st : St kappa pp) →
    (x : Fin (C.pubLen.eval kappa) → Bool) → (f : Fin (C.fnLen.eval kappa) → Bool) →
    (mu : C.Out kappa (S.cprm kappa pp)) → KeyDraw kappa pp st x f mu →
    S.SK kappa pp × St kappa pp
  /-- Encode a complete setup draw. -/
  encSetupDraw : (kappa : ℕ) → (pp : PublicParams S.G kappa) → SetupDraw kappa pp → List Bool
  /-- Encode a complete ciphertext-simulation draw. -/
  encEncDraw : (kappa : ℕ) → (pp : PublicParams S.G kappa) → (st : St kappa pp) →
    (x : Fin (C.pubLen.eval kappa) → Bool) → EncDraw kappa pp st x → List Bool
  /-- Encode a complete key-simulation draw. -/
  encKeyDraw : (kappa : ℕ) → (pp : PublicParams S.G kappa) → (st : St kappa pp) →
    (x : Fin (C.pubLen.eval kappa) → Bool) → (f : Fin (C.fnLen.eval kappa) → Bool) →
    (mu : C.Out kappa (S.cprm kappa pp)) → KeyDraw kappa pp st x f mu → List Bool

namespace SASimulator.Raw

variable {S} (Sim : SASimulator.Raw S)

instance instSetupFinite (kappa : ℕ) (pp : PublicParams S.G kappa) :
    Fintype (Sim.SetupDraw kappa pp) := Sim.setupFinite kappa pp

instance instSetupNonempty (kappa : ℕ) (pp : PublicParams S.G kappa) :
    Nonempty (Sim.SetupDraw kappa pp) := Sim.setupNonempty kappa pp

instance instEncFinite (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) : Fintype (Sim.EncDraw kappa pp st x) :=
  Sim.encFinite kappa pp st x

instance instEncNonempty (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) : Nonempty (Sim.EncDraw kappa pp st x) :=
  Sim.encNonempty kappa pp st x

instance instKeyFinite (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) (f : Fin (C.fnLen.eval kappa) → Bool)
    (mu : C.Out kappa (S.cprm kappa pp)) : Fintype (Sim.KeyDraw kappa pp st x f mu) :=
  Sim.keyFinite kappa pp st x f mu

instance instKeyNonempty (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) (f : Fin (C.fnLen.eval kappa) → Bool)
    (mu : C.Out kappa (S.cprm kappa pp)) : Nonempty (Sim.KeyDraw kappa pp st x f mu) :=
  Sim.keyNonempty kappa pp st x f mu

/-- A ciphertext-simulation input contains pp, the private state and public input. -/
structure EncInput (kappa : ℕ) where
  /-- The public parameters. -/
  pp : PublicParams S.G kappa
  /-- The current simulator state. -/
  state : Sim.St kappa pp
  /-- The public challenge input. -/
  publicInput : Fin (C.pubLen.eval kappa) → Bool

/-- A key-simulation input additionally contains the requested function and allowed scalar. -/
structure KeyInput (kappa : ℕ) where
  /-- The public parameters. -/
  pp : PublicParams S.G kappa
  /-- The current simulator state. -/
  state : Sim.St kappa pp
  /-- The public challenge input. -/
  publicInput : Fin (C.pubLen.eval kappa) → Bool
  /-- The requested function. -/
  function : Fin (C.fnLen.eval kappa) → Bool
  /-- The allowed scalar, before target-group embedding. -/
  value : C.Out kappa (S.cprm kappa pp)

/-- The ciphertext-simulation parameter word excludes the private input. -/
def encInputWord (kappa : ℕ) (pi : Sim.EncInput kappa) : List Bool :=
  pairEncode pi.pp.encode (pairEncode (List.ofFn (Sim.encSt kappa pi.pp pi.state))
    (List.ofFn pi.publicInput))

/-- The ciphertext parameter word has exactly the displayed public information. -/
theorem encInputWord_eq (kappa : ℕ) (pi : Sim.EncInput kappa) :
    Sim.encInputWord kappa pi = pairEncode pi.pp.encode
      (pairEncode (List.ofFn (Sim.encSt kappa pi.pp pi.state)) (List.ofFn pi.publicInput)) := rfl

/-- The key-simulation word encodes the state, public input, function and scalar. -/
def keyInputWord (kappa : ℕ) (pi : Sim.KeyInput kappa) : List Bool :=
  pairEncode pi.pp.encode (pairEncode (List.ofFn (Sim.encSt kappa pi.pp pi.state))
    (pairEncode (List.ofFn pi.publicInput)
      (pairEncode (List.ofFn pi.function) (C.encValue kappa (S.cprm kappa pi.pp) pi.value))))

/-- The key-simulation word has the displayed nested-pair encoding. -/
theorem keyInputWord_eq (kappa : ℕ) (pi : Sim.KeyInput kappa) :
    Sim.keyInputWord kappa pi = pairEncode pi.pp.encode
      (pairEncode (List.ofFn (Sim.encSt kappa pi.pp pi.state))
        (pairEncode (List.ofFn pi.publicInput)
          (pairEncode (List.ofFn pi.function)
            (C.encValue kappa (S.cprm kappa pi.pp) pi.value)))) := rfl

/-- Simulated setup applies its deterministic core to one exact complete draw. -/
noncomputable def setup (kappa : ℕ) (pp : PublicParams S.G kappa) :
    ProbComp (S.MPK kappa pp × Sim.St kappa pp) :=
  Sim.setupCore kappa pp <$> ProbComp.sample (Sim.SetupDraw kappa pp)

/-- The setup law is the displayed pushforward of its complete draw. -/
theorem setup_eq (kappa : ℕ) (pp : PublicParams S.G kappa) :
    Sim.setup kappa pp = Sim.setupCore kappa pp <$> ProbComp.sample (Sim.SetupDraw kappa pp) :=
  rfl

/-- Ciphertext simulation sees only the public input and threads its state. -/
noncomputable def enc (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) : ProbComp (S.CT kappa pp × Sim.St kappa pp) :=
  Sim.encCore kappa pp st x <$> ProbComp.sample (Sim.EncDraw kappa pp st x)

/-- The ciphertext law is the displayed pushforward of its complete draw. -/
theorem enc_eq (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) : Sim.enc kappa pp st x =
    Sim.encCore kappa pp st x <$> ProbComp.sample (Sim.EncDraw kappa pp st x) := rfl

/-- Key simulation sees the queried function and its allowed scalar and threads state. -/
noncomputable def key (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) (f : Fin (C.fnLen.eval kappa) → Bool)
    (mu : C.Out kappa (S.cprm kappa pp)) : ProbComp (S.SK kappa pp × Sim.St kappa pp) :=
  Sim.keyCore kappa pp st x f mu <$> ProbComp.sample (Sim.KeyDraw kappa pp st x f mu)

/-- The key law is the displayed pushforward of its complete draw. -/
theorem key_eq (kappa : ℕ) (pp : PublicParams S.G kappa) (st : Sim.St kappa pp)
    (x : Fin (C.pubLen.eval kappa) → Bool) (f : Fin (C.fnLen.eval kappa) → Bool)
    (mu : C.Out kappa (S.cprm kappa pp)) : Sim.key kappa pp st x f mu =
    Sim.keyCore kappa pp st x f mu <$> ProbComp.sample (Sim.KeyDraw kappa pp st x f mu) := rfl

end SASimulator.Raw

/-- A semi-adaptive simulation interface carries uniform efficiency for all three
samplers. [Wee20, §2.2, p.5; AGW20, §4.1, pp.11–12]. The shared contract chooses
one sampler/core witness before kappa and every public input. The private state has one
fixed polynomial bit width. -/
structure SASimulator extends SASimulator.Raw S where
  /-- Setup and its encoded public key/state output are uniformly efficient. -/
  setup_eff : SamplesEfficiently
    (fun kappa (pp : PublicParams S.G kappa) => pp.encode) encSetupDraw
    (fun kappa pp (o : S.MPK kappa pp × St kappa pp) =>
      pairEncode (List.ofFn (S.encMPK kappa pp o.1)) (List.ofFn (encSt kappa pp o.2))) setupCore
  /-- Public-input-only ciphertext simulation is uniformly efficient. -/
  enc_eff : SamplesEfficiently toRaw.encInputWord
    (fun kappa pi => encEncDraw kappa pi.pp pi.state pi.publicInput)
    (fun kappa pi (o : S.CT kappa pi.pp × St kappa pi.pp) =>
      pairEncode (List.ofFn (S.encCT kappa pi.pp o.1)) (List.ofFn (encSt kappa pi.pp o.2)))
    (fun kappa pi => encCore kappa pi.pp pi.state pi.publicInput)
  /-- Key simulation is uniformly efficient with all permitted inputs on its word. -/
  key_eff : SamplesEfficiently toRaw.keyInputWord
    (fun kappa pi => encKeyDraw kappa pi.pp pi.state pi.publicInput pi.function pi.value)
    (fun kappa pi (o : S.SK kappa pi.pp × St kappa pi.pp) =>
      pairEncode (List.ofFn (S.encSK kappa pi.pp o.1)) (List.ofFn (encSt kappa pi.pp o.2)))
    (fun kappa pi => keyCore kappa pi.pp pi.state pi.publicInput pi.function pi.value)

namespace SASimulator

variable {S} (Sim : SASimulator S)

/-- The raw projection preserves the semi-adaptive simulator's polynomial state width. -/
theorem toRaw_stLen : Sim.toRaw.stLen = Sim.stLen := rfl

/-- The raw projection preserves the semi-adaptive simulator's private-state family. -/
theorem toRaw_St : Sim.toRaw.St = Sim.St := rfl

/-- The raw projection preserves the semi-adaptive simulator's private-state encoding. -/
theorem toRaw_encSt : Sim.toRaw.encSt = Sim.encSt := rfl

/-- The raw projection preserves the semi-adaptive simulator's deterministic setup core. -/
theorem toRaw_setupCore : Sim.toRaw.setupCore = Sim.setupCore := rfl

/-- The raw projection preserves the public-input-only deterministic ciphertext core. -/
theorem toRaw_encCore : Sim.toRaw.encCore = Sim.encCore := rfl

/-- The raw projection preserves key simulation from its function and allowed scalar. -/
theorem toRaw_keyCore : Sim.toRaw.keyCore = Sim.keyCore := rfl

end SASimulator

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw
