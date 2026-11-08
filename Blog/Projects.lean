import VersoBlog

open Verso Genre Blog

#doc (Page) "Projects" =>

These projects explore the core ideas of verified systems programming on small, self-contained
examples before applying those ideas to PL/OS. Each project develops an executable model,
precise contracts, and proofs, with agents assisting in implementation and proof construction.

1. [A Small Allocator](projects/allocator/): allocation invariants, finite addresses, freshness,
   failure, and preservation of unrelated state.
1. [A Bounded Queue](projects/queue/): representation invariants, circular buffers, refinement,
   and composition over sequences of operations.
1. [A Small RISC Machine](projects/machine/): instruction semantics, finite arithmetic,
   execution traces, loop invariants, and termination.
1. [A Small Verified Compiler](projects/compiler/): source semantics, code generation,
   branch layout, and compositional compiler correctness.
1. [Protected Memory and Isolation](projects/protection/): whole-access authorization,
   failure atomicity, byte frames, and isolation across command sequences.
1. [A Cooperative Scheduler](projects/scheduler/): context ownership, live and saved state,
   scheduling invariants, and simulation across context switches.
