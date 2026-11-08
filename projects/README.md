# Teaching projects

These projects explore core ideas on small systems before applying them to PL/OS.
They live in the course repository for now. Each project is an independent Lake
package: build it from its own directory, without building the website or cloning
`plos-risc`. The [Projects page](https://plum-umd.github.io/cmsc818c/projects/)
contains the student-facing assignments. The website checks project examples
against the same source files using its own toolchain.

| Project | Status | Main ideas |
| --- | --- | --- |
| [Allocator](https://plum-umd.github.io/cmsc818c/projects/allocator/) | Executable model, checks, and proof exercises | Contracts, finite addresses, freshness, failure, frames |
| [Queue](https://plum-umd.github.io/cmsc818c/projects/queue/) | Executable reference, circular-buffer starter, checks, and proof exercises | Representation invariants and refinement |
| [Small RISC machine](https://plum-umd.github.io/cmsc818c/projects/machine/) | Executable instruction model, checks, and proof exercises | Instruction semantics, loops, faults, and termination |
| [Small compiler](https://plum-umd.github.io/cmsc818c/projects/compiler/) | Source semantics, compiler, checks, and proof exercises | State correspondence, code layout, and semantic preservation |
| [Protected memory](https://plum-umd.github.io/cmsc818c/projects/protection/) | Executable service, access and byte specifications, checks, and proof exercises | Authority, failure atomicity, framing, and trace isolation |
| [Cooperative scheduler](https://plum-umd.github.io/cmsc818c/projects/scheduler/) | Abstract scheduler, context manager, checks, and proof exercises | Context ownership, lifecycle invariants, simulation, and frames |

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
obligations and how to work with an agent. Use `cd projects/queue` from the repository
root to build the queue project in the same way, or `cd projects/machine` for the
RISC machine project.
The protected-memory project builds from `projects/protection`.
The cooperative scheduler builds from `projects/scheduler` and uses the supplied
machine context and protection-domain definitions through local Lake dependencies.

The compiler project uses the machine package through a local Lake dependency.
It needs the supplied machine definitions, not student solutions to Project 3.
The compiler and machine share one instruction model rather than maintaining copies.
