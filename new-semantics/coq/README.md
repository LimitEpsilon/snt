# Coq Proofs for Modular Analysis

## Proving Simulation with Backpatching

- Definition for semantics without memory: [eval](./sim/EnvSemantics.v#L21)
- Definition for semantics with memory: [meval](./sim/MemSemantics.v#L15)
- Simulation: [sim_semantics](./sim/MemSemantics.v#L677)

## Proving Advance

- Definition for semantics with events: [eval](./events/EnvSemantics.v#L22)
- Definition for linking: [link](./events/LinkDefs.v#L22)
- Advance: [advance](./events/Advance.v#L173)