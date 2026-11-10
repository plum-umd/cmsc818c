# Possible follow on projects in PL/OS

November 10, 2026. Planning ideas to revisit after further PL/OS development, not settled
assignments or a required course sequence.

The proposed course endpoint is a verified systems component with a demonstrated connection
to a larger system. A complete verified RISC kernel can remain the research direction
without becoming the minimum student deliverable. The existing nine projects should be a
menu: assigning all nine and then all of the work below would leave too little capstone time.

## Development baseline

The discussion used the local `plos-risc` checkout at commit
`0cbcf49820d491b4ce185053ef8abeb0125b37bd`, together with working-tree changes including
the uncommitted choice-traversal implementation and its integration. Source paths below
refer to that repository. Its [documentation](https://github.com/plum-umd/plos-risc/tree/main/docs)
describes the evolving component boundaries.

The development now includes a shared arena, native process and offer records, scheduler
selection, FIFO partner search, offer registration and retirement, and whole-event choice
traversal. These support projects about composition, search order, representation, ownership,
and publication, rather than simply larger assembly programs.

The shared kernel's `SharedExecutionProof.run_correct` assumes successful native execution.
Finite-resource adequacy remains a separate obligation. Native traps, context switching,
and correspondence to physical hardware also remain outside these component guarantees.
A complete native kernel would combine several substantial projects beyond the ones below.

The course starters currently pin an older PL/OS revision. Reusing newer infrastructure
will require committing the relevant upstream work and deliberately updating the course pins.

## Suggested progression

### A guided lab on subroutine composition

`Plos/RiscV/Composition.lean` provides a particularly bounded exercise: six caller
instructions reserve a stack frame, save `ra`, invoke lookup, restore the frame, and return.
Students implement the caller and prove its contract using the supplied lookup theorem.

The central lesson is that independently correct routines need contracts strong enough to
compose. Stack writes must preserve code and table data, saved registers must survive, and
an inner return must not be confused with completion of the outer call. A result-only
callee theorem is insufficient when the harness can observe the outer return marker during
execution; an execution segment with a PC footprint supports the required composition.

Supply `Segment`, its composition lemmas, the strengthened lookup contract, image loading,
and suitable stack-address arithmetic helpers. Students should prove the caller's result,
termination bound, restored `ra` and `sp`, and exact saved-return-address memory effect.
Releasing the stack frame does not erase its saved bytes.

This is best treated as a short guided lab, potentially immediately after lookup, rather
than another large mandatory assignment.

### A project on FIFO rendezvous partner search

`Plos/RiscV/Partner.lean` is the strongest candidate for the next substantial project.
Its 17-instruction routine searches one channel's offer row, skips the wrong direction
and offers from the caller, and returns the first eligible partner.

Specify the result as the first offer with the desired direction and an allowed PID, or
absence if none exists. Require memory and register frames and termination within a linear
instruction bound. Finding some eligible offer is insufficient: the first-match property
establishes the required FIFO behavior.

The main loop invariant records that every offer already passed was ineligible. The
remaining count supplies a decreasing measure. The empty case should require no data load.
The host wrapper must handle an oversized natural-number caller PID without truncation
accidentally excluding a different process.

Supply the five-word record layout, validated-row representation, code-loading infrastructure,
and payload-resolution boundary. Limit the main assignment to one channel row, leaving
whole-event traversal and offer-store reconstruction outside its core scope. This brings
students into communication semantics while keeping the machine-level task manageable.

### One bounded capstone

Offer a choice of components with explicit contracts and supplied infrastructure.

| Candidate | Central lesson | Suggested scope |
| --- | --- | --- |
| Scheduler selection | Validating a native-to-host handoff | Implement the read-only probe in `Plos/RiscV/Select.lean`, distinguish idle, missing, non-runnable, and corrupt cases, and connect a selected result to the current process record. Supply directory and queue operations. |
| Stable offer retirement | A writing loop that preserves a representation | Filter one channel row, remove every matching PID, retain survivor order and payload references, rebuild canonical links, and frame unrelated memory. Supply allocation and the multi-channel wrapper. |
| Whole-event choice search | Composing two ordered searches | Extend partner search across alternatives, preserving alternative order, FIFO order within each row, the original alternative index, and the proper message-registry interpretation. Supply event preparation and validation. |
| Process-record publication | Representation, ownership, and publication | Build and validate a fresh record version, preserve existing registry references and unrelated allocations, and publish its directory entry only after preparation succeeds. Supply native word operations and allocation. |

Partner search followed by single-row retirement is the preferred sequence to explore.
Students first prove which offer wins, then prove how obsolete offers are removed. The
integration goal is that a process's other pending alternatives cannot remain available
after its communication has committed. A one-row theorem needs an explicit connection to
the supplied multi-channel retirement and communication policy to establish that goal.

Retirement should not be assigned by simply deleting the entire reference implementation
and proof. At this baseline, `Plos/Kernel/NativeRetire.lean` is roughly 1,200 lines, including
instruction and framing infrastructure. Expose a few central obligations: one iteration,
the loop invariant, stable filtering, canonical output, and the write footprint. Supply
the surrounding helpers.

Whole-event choice is a natural advanced extension after partner search. The current
`Plos/RiscV/ChoiceProof.lean` is roughly 750 lines, so it should not automatically become
the next required assignment. Its two search orders, original alternative indices, and
distinct message registries add meaningful obligations beyond a single-row scan.

For publication projects, distinguish preservation of published allocations from the
functional rollback behavior of `StateT Machine (Except String)`. A failed raw instruction
sequence may have performed stores. Retaining an old immutable machine value does not
establish physical hardware transactions or crash consistency.

## A resource accounting alternative

A useful capstone could require little new assembly: prove sufficient arena space for
one operation or a bounded workload. Repeated process-record versions, directory updates,
and choice staging consume fresh space even when the logical state remains small.

Choose a concrete operation or workload, state bounds on its inputs and number of steps,
derive a sufficient allocation budget, and prove that the relevant resource checks succeed.
This would strengthen the existing success-conditional correspondence results without
requiring general reclamation, arbitrary-program termination, or an entire native kernel.

## Course workload and deliverables

A plausible course selects introductory exercises, uses composition as a guided lab,
requires partner search, and ends with one capstone. The exact selection should follow
instructor dry runs of the existing assignments and their universal proof obligations.

Each capstone should deliver an implementation, a substantive contract, a machine-checked
proof, and one explicit integration theorem. The integration theorem should explain how
the local guarantee contributes to the larger system while retaining its stated assumptions.
Agent use should be assessed through specification review, proof decomposition, diagnosis
of incorrect proposals, and an explanation of the final verification boundary.

## Questions to revisit

- Which newer components and interfaces have stabilized enough to pin for a semester?
- Which existing projects are required, guided labs, or reference material?
- Does the next main project remain single-channel partner search, or has another boundary
  become substantially clearer or smaller?
- How much instruction bookkeeping can reusable execution and framing lemmas remove?
- Can the retirement assignment stay confined to one row with a supplied integration wrapper?
- Should the final integration claim concern one operation, a bounded workload, or a whole
  scheduler execution through an existing replacement theorem?
- Is bounded resource adequacy a better capstone than additional native control flow?
- What source, ABI, allocator, registry, ownership, and hardware assumptions must students
  state explicitly for each candidate?

Revisit these choices after additional PL/OS work and instructor proof dry runs. Avoid
turning this list into an automatic sequence of further mandatory projects.
