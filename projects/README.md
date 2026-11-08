# Teaching projects

These projects explore core ideas on small systems before applying them to PL/OS.
They live in the course repository for now. Each project is an independent Lake
package: build it from its own directory, without building the website or cloning
`plos-risc`. The [Projects page](https://plum-umd.github.io/cmsc818c/projects/)
contains the student-facing assignments. The website checks allocator examples
against the same source files using its own toolchain.

| Project | Status | Main ideas |
| --- | --- | --- |
| [Allocator](https://plum-umd.github.io/cmsc818c/projects/allocator/) | Executable model, checks, and proof exercises | Contracts, finite addresses, freshness, failure, frames |
| Queue | Existing [notes and checked examples](../Blog/Examples/); standalone project planned | Representation invariants and refinement |
| Tiny machine | Planned | Instruction semantics, execution invariants, faults |
| Tiny compiler | Planned | Simulation and semantic preservation |
| Protection | Planned | Authority, isolation, and shared state |

This is a roadmap, not a fixed assignment schedule. Projects need not implement
components that will be reused by PL/OS. The proof techniques and explicit
assumptions are what should transfer. A compiler exercise may use a stack machine
even though a later project targets a register machine.

## Project boundaries

- Give each project its own `lean-toolchain`, Lake configuration, README, and checks.
- Use Lean/Std alone where possible. Do not depend on a sibling checkout or the
  website's Verso toolchain.
- State which artifacts are supplied and which proofs students must construct.
  Keep unfinished exercises out of the checked reference library.
- Provide a starting point that does not require solving an earlier project.
- Record model choices and their correspondence to PL/OS; consistency is a design
  goal, not a claim of a proved refinement to PL/OS or physical hardware.
- Keep support code local until multiple projects actually need the same interface.
  Shared models can then become a local package, or an independent repository.

The allocator starts with the same Lean 4.27.0 toolchain as the inspected PL/OS
checkout. Each package can move independently if that later becomes useful.

## Building

```sh
cd projects/allocator
lake build
```

The build includes executable regression checks. See the project README for proof
obligations and how to work with an agent. Website builds remain unchanged.
