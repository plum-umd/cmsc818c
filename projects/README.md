# Teaching projects

These projects explore core ideas on small systems before applying them to PL/OS.
They live in the course repository for now. Each project is an independent Lake
package: build it from its own directory, without building the website or maintaining
a sibling `plos-risc` checkout. The [Projects page](https://plum-umd.github.io/cmsc818c/projects/)
contains the student-facing assignments. The website checks excerpts against the
actual starter source; the PL/OS assignments use cross-toolchain extraction.

| Project | Status | Main ideas |
| --- | --- | --- |
| [Allocator](https://plum-umd.github.io/cmsc818c/projects/allocator/) | Executable model, checks, and proof exercises | Contracts, finite addresses, freshness, failure, frames |
| [Queue](https://plum-umd.github.io/cmsc818c/projects/queue/) | Executable reference, circular-buffer starter, checks, and proof exercises | Representation invariants and refinement |
| [Small RISC machine](https://plum-umd.github.io/cmsc818c/projects/machine/) | Executable instruction model, checks, and proof exercises | Instruction semantics, loops, faults, and termination |
| [Small compiler](https://plum-umd.github.io/cmsc818c/projects/compiler/) | Source semantics, compiler, checks, and proof exercises | State correspondence, code layout, and semantic preservation |
| [Protected memory](https://plum-umd.github.io/cmsc818c/projects/protection/) | Executable service, access and byte specifications, checks, and proof exercises | Authority, failure atomicity, framing, and trace isolation |
| [Cooperative scheduler](https://plum-umd.github.io/cmsc818c/projects/scheduler/) | Abstract scheduler, context manager, checks, and proof exercises | Context ownership, lifecycle invariants, simulation, and frames |
| [RISC lookup](https://plum-umd.github.io/cmsc818c/projects/risc-lookup/) | Assembly starter, contracts, fixtures, and proof exercises | Encoded execution, calling conventions, and read-only refinement |
| [RISC handles](https://plum-umd.github.io/cmsc818c/projects/risc-handles/) | Append and persistent-adapter starters, verified loader, checks, and proof exercises | Exact writes, code frames, persistence, and component composition |

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

The RISC lookup project starts the PL/OS component sequence. It pins PL/OS revision
`06668a4d6bec72a4ccf65dc48093e984d6960ce6` and imports only its machine, assembler,
code-image, and call infrastructure. It does not import the completed lookup.
Its source-highlighting dependency is pinned separately for Verso extraction on Lean 4.27.0.
When maintaining those pins, use `lake --keep-toolchain update` to retain the assignment's
toolchain; SubVerso's own default toolchain can be newer than the versions it supports.
Run `lake build` in `projects/risc-lookup` for the starter checks. After implementing the
routine, run `lake exe check-lookup`; this second command intentionally fails on the
empty starter. The universal exercise propositions remain student obligations.

The handles project uses the same pins and supplies the upstream lookup solution, but
does not import upstream append or native handles. Its generic loader admits the student's
append code. Run the starter build in `projects/risc-handles`, then run
`lake exe check-handles` after implementing both the routine and persistent adapter.
