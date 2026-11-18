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
