namespace SASimulator

variable {S} (Sim : SASimulator S)

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
