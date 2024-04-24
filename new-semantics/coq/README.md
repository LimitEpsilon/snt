# Coq Proofs for Modular Analysis

## Proving Simulation with Backpatching

- Definition for semantics without memory: [eval](./sim/EnvSemantics.v#L21)
- Definition for semantics with memory: [meval](./sim/MemSemantics.v#L15)
- Definition for simulation: [sim](./sim/Defs.v/#L326), [Sim](./sim/MemSemantics.v/#L205)
- Simulation: [sim_semantics](./sim/MemSemantics.v#L677), [sim_empty](./sim/MemSemantics.v#L696)

## Proving Advance

- Definition for semantics with events: [eval](./events/EnvSemantics.v#L27)
- Definition for linking: [link](./events/LinkDefs.v#L21)
- Advance: [advance](./events/Advance.v#L172)
