# Course development: what to work on next

Updated November 8, 2026. These are development priorities, not settled course requirements.

## Course direction

Explore core verification ideas through small, self-contained projects, then apply those ideas
inside `plos-risc`. The preliminary implementations need not become PL/OS components; their
specifications, invariants, refinement arguments, and proof techniques should transfer.

The preliminary sequence is now developed far enough to transition into PL/OS. Do not add
another standalone project by default. The pacing risk is requiring so much preliminary work
that students reach the larger system too late: six complete proof assignments plus their
extensions could consume substantial course time.

The earlier plan prioritized a complete list-to-buffer-to-RISC queue development before PL/OS.
The current sequence broadens that preparation to six projects. A machine-level queue routine
could still be a useful integration task, but it is no longer a prerequisite for every later topic.

## Work completed

- [x] Organize the [course notes](Blog/Notes.lean) into a suggested reading order and mark stubs.
- [x] Develop lessons on specifications, operational semantics, invariants, executable
  specifications, representation invariants, and refinement and simulation.
- [x] Provide an abstract queue model, executable circular buffer, regression examples,
  and worked buffer-to-list and finite-trace proofs.
- [x] Establish a modest teaching machine: 64-bit words, registers, signed immediates,
  arithmetic, branches, explicit faults, and fuel-bounded execution over decoded instructions.
- [x] Add a [Projects section](Blog/Projects.lean) with six student-facing Verso assignments,
  anchored source excerpts, and checked examples.
- [x] Organize independently buildable project packages under [projects/](projects/README.md),
  with regression checks, assumption-audit entry points, and CI configuration.
- [x] State milestones, assumptions, proof obligations, and expectations for students'
  explanations and use of agents. Separate optional extensions where appropriate.
- [x] Reuse supplied machine definitions through local dependencies when projects need them,
  rather than duplicating the machine model or requiring earlier student solutions.

### The preliminary projects

| Project | Main teaching idea |
| --- | --- |
| [Allocator](Blog/Projects/Allocator.lean) | Contracts; direct preservation versus specification preservation and conformance |
| [Queue](Blog/Projects/Queue.lean) | Representation invariants, relational simulation, and trace composition |
| [Machine](Blog/Projects/Machine.lean) | Instruction semantics, faults, finite arithmetic, loop invariants, and termination |
| [Compiler](Blog/Projects/Compiler.lean) | Source semantics, register correspondence, branch layout, and compositional translation |
| [Protection](Blog/Projects/Protection.lean) | Whole-access authorization, byte frames, failure atomicity, and trace isolation |
| [Scheduler](Blog/Projects/Scheduler.lean) | Live versus parked contexts, active domains, lifecycle invariants, and simulation |

These are assignment descriptions and checked starter artifacts. Most exercise propositions
are deliberately unproved. Successful builds check the supplied code, examples, and baseline
lemmas; they do not establish that the student obligations have been completed.

The queue definitions now live in `projects/queue/Queue/`. Worked circular-buffer proofs remain
in `Blog/Examples/CircularBuffer.lean`, with regression examples in
`Blog/Examples/CircularBufferChecks.lean`.

## Immediate priority: transition into PL/OS

- [ ] Define the minimum capstone: one bounded, reviewable contribution to `plos-risc`, with
  an explicit specification, implementation, tests, proofs, and statement of assumptions.
  A complete operating system is not the minimum deliverable.
- [ ] Choose one existing operation for a guided entry assignment. Trace it through its
  specification, implementation, representation, and correctness theorem.
- [ ] Ask students to audit that operation's guarantees: failure behavior, preserved state,
  assumptions, and the connection to executable code.
- [ ] Select a small modification or additional operation. Identify the proofs it should
  reuse, the claims it changes, and the new obligations it introduces.
- [ ] Explain how the resulting guarantee composes with the rest of the system.

Message passing, blocking, cancellation, and richer scheduling should now be developed in
PL/OS where practical, rather than automatically becoming more preliminary toy projects.
A focused explanatory model may still be useful when a particular concept needs it.

## Validate the teaching workload

- [ ] Decide which preliminary projects are required submissions, guided exercises, or
  reference material. Do not assume every student must finish all extensions before PL/OS.
- [ ] Allocate course time so substantial work remains for processes, communication, and
  integration in the larger system.
- [ ] Dry-run the assignments and develop instructor reference solutions. Confirm that the
  stated proof obligations are attainable with the supplied interfaces and support lemmas.
- [ ] Estimate the effort spent on arithmetic, array lemmas, and proof tooling; provide more
  support where that effort obscures the intended systems lesson.
- [ ] Add assessment rubrics. Existing milestones and write-up instructions are not yet a
  complete grading policy.
- [ ] Decide how explanations, specification review, tests, proof audits, and implementation
  variations demonstrate understanding when agents and worked examples are available.

## Remaining writing and examples

The project pages now introduce many ideas from the old writing plan, but the dedicated
notes are not all developed. Several remain explicitly marked as stubs.

- [ ] Develop or link the notes on finite arithmetic, machine execution, machine routines,
  framing, and proof composition using the project examples. Avoid duplicating explanations
  without a clear role in the reading sequence.
- [ ] Add a concrete interference example showing where the sequential queue proof's
  exclusive-access assumption fails and what mechanism restores correctness.
- [ ] Distinguish safety, termination, deadlock freedom, starvation freedom, and fairness
  through concrete system behaviors. Cooperative scheduling cannot guarantee cooperation.
- [ ] Develop proof-engineering examples: strengthen an invariant, factor a theorem, and
  diagnose implementation bugs, specification bugs, and overstrong claims.
- [ ] Demonstrate reviewing agent-generated proof repairs while preserving the intended claim.
- [ ] Develop the blocking and rendezvous material alongside the chosen PL/OS operation.

Separation-logic machinery is still a possible teaching tool, not a prerequisite or a settled
framework choice. The allocation and protection projects already provide concrete interval,
framing, and ownership questions against which to evaluate its usefulness.

## Keep the verification boundary explicit

- [ ] Identify the calling convention, execution environment, and executable artifact needed
  by the chosen PL/OS contribution.
- [ ] Trace the connection from the proved model to running instructions, including assembly
  or code generation and assumptions about the platform and hardware.
- [ ] Document which parts are proved and which remain trusted at each integration boundary.

The teaching machine executes decoded instruction arrays. The compiler targets that model;
its proof exercises do not by themselves establish correctness of emitted native binaries.
The protection service assumes a trusted caller identity and a valid host policy. The
scheduler uses atomic kernel events and selects domain metadata; it does not establish
hardware trap entry, preemption, or physical enforcement of permissions.

The complete queue-to-RISC routine proof and a connection to physical hardware remain
unfinished. Decide whether either is necessary for the selected capstone before making it
mandatory development work.

## Suggested restart point

Inspect `../plos-risc/` and choose the operation for the guided transition assignment.
Write down its existing contract and proof boundary, then propose one small change with
clear integration obligations. In parallel, decide how much of the preliminary sequence
will be required and schedule an instructor dry run of those assignments.

After changing Lean examples or posts, build and regenerate the website:

```sh
lake build
lake exe generate-blog
```

Build each standalone teaching project from its own directory with `lake build`.
