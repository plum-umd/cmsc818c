# Course development: what to work on next

Planning notes, November 7, 2026. These are proposed priorities, not settled course requirements.

## Course direction

Follow one system from an abstract specification to executable code, using agents to help
construct implementations and proofs while keeping the claims independently checkable.
Use the bounded queue as a compact introduction and PL/OS as the larger destination.

The main pacing risk is spending so long on the verification machinery that students reach
processes, communication, and isolation too late. Develop a complete path through the queue,
then revisit its techniques in systems components. Prioritize concrete examples over more titles.

## Where we are

- [Course table of contents](Blog/Notes.lean): grouped reading order, with unfinished posts marked.
- Six developed lessons: specifications, operational semantics, invariants and induction,
  executable specifications, representation invariants, and refinement and simulation.
- [Abstract queue model](Blog/Examples/Queue.lean): transition rules, executable list model,
  preservation, reachability, determinism, and semantic agreement proofs.
- [Circular buffer](Blog/Examples/CircularBuffer.lean): initialization, invariant preservation,
  operation-level simulation, and agreement of complete finite command sequences.
- [Concrete checks](Blog/Examples/CircularBufferChecks.lean): wraparound, capacity one,
  duplicate values, stored zero, and full and empty cases.
- The RISC implementation and its machine-level proofs remain future work.
- The larger course project starts in `../plos-risc/`.

## First decisions

- [ ] Choose the initial RISC architecture, supported instruction subset, and execution environment.
  Record the machine semantics, memory model, calling convention, and intended relationship
  between modeled instructions and executable artifacts. Keep the initial scope modest.
- [ ] Define the minimum capstone. A candidate is one PL/OS component with a proved machine-level
  contract connected to its abstract interface. Treat a complete OS as an ambitious extension.
- [ ] Define what students must demonstrate themselves: understanding the specification,
  invariant, proof structure, assumptions, and agent-generated changes.
- [ ] Allocate time so the sequential warm-up leaves substantial room for concurrency and OS work.

## Next implementation and writing sequence

1. **Finite arithmetic.** Relate natural-number indices and counts to machine words. Establish
   capacity and address bounds, and handle overflow in circular-buffer index calculations.
2. **Machine execution in Lean.** Define or adopt the selected instruction semantics and run
   small instruction sequences. Explain registers, memory, faults, and execution traces.
3. **One verified RISC queue routine.** Implement a queue operation and prove its entry/exit
   contract, termination, valid memory accesses, and preservation of required registers and memory.
4. **Compose the proofs.** Connect machine state to the circular buffer, then reuse the existing
   buffer-to-list refinement. State the resulting guarantee and remaining trusted assumptions.
5. **A small rendezvous example.** Introduce processes, blocking, and synchronous communication
   without immediately taking on the whole PL/OS implementation. Use it to expose the new
   obligations introduced by concurrency.

Done for this phase means students can inspect a complete path from an abstract queue rule
to a checked claim about the instructions implementing it.

## Topics to strengthen with concrete examples

### Ownership and memory reasoning

- [ ] Describe allocated regions, disjointness, aliasing, and preservation of unrelated state.
- [ ] Introduce separation-logic ideas where useful; choose a framework only if it helps the work.
- [ ] Connect these ideas to the existing post on frame properties.

### Concurrency and interference

- [ ] Show exactly where the sequential queue proof relies on exclusive access.
- [ ] Give an execution where another process or interrupt handler invalidates that reasoning.
- [ ] Explain the mechanism and contract needed to restore correctness.

### Progress and resource bounds

- [ ] Distinguish safety, termination, deadlock freedom, starvation freedom, and fairness.
- [ ] Include a system that preserves its safety invariants but makes no useful progress.
- [ ] Make resource exhaustion and scheduler assumptions explicit.

### The verification boundary

- [ ] Trace the connection from a Lean theorem to running instructions, including code generation
  or assembly, calling conventions, the execution platform, and hardware assumptions.
- [ ] Distinguish properties established in the model from assumptions about the actual platform.

### Proof engineering and diagnosis

- [ ] Develop worked examples of finding and strengthening an invariant.
- [ ] Show how to split a correctness theorem into reusable lemmas.
- [ ] Include failed attempts that expose an implementation bug, a specification bug, or an
  overstrong theorem, and explain how to distinguish them.
- [ ] Demonstrate reviewing agent-generated proof repairs without silently changing the claim.

## Design an assignment alongside the material

- [ ] Write one assignment with explicit milestones and a rubric before filling every remaining stub.
- [ ] Include specification review, implementation, tests, proofs, and an explanation of assumptions.
- [ ] Require students to explain the important claims and decisions, including agent-assisted work.
- [ ] Use the assignment to identify missing prerequisites and estimate the workload.

## Suggested restart point

Resolve the RISC target and execution environment first. Then develop **Finite Arithmetic**
against the existing circular buffer and draft the first machine-routine assignment alongside it.

Build and regenerate the site after changes to the Lean examples or posts:

```sh
lake build
lake exe generate-blog
```
