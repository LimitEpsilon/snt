# Coq Proofs for Modular Analysis

## Proving Simulation with Backpatching

- Definition for semantics without memory: [eval](./sim/EnvSemantics.v#L21)
- Definition for semantics with memory: [meval](./sim/MemSemantics.v#L15)
- Definition for simulation: [sim](./sim/Defs.v/#L326), [Sim](./sim/MemSemantics.v/#L205)
- Simulation: [sim_semantics](./sim/MemSemantics.v#L677), [sim_empty](./sim/MemSemantics.v#L696)

## Proving Advance

- Definition of semantic domains, and the smart constructor `predE`: [Defs](./events/Defs.v)
- Definition for semantics with events: [eval](./events/EnvSemantics.v)
- Definition for linking: [link](./events/LinkDefs.v)
- Advance: [advance](./events/Advance.v)
