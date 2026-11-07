import VersoBlog

open Verso Genre Blog

#doc (Post) "PL/OS: From a Lean Prototype to Verified RISC Code" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

Our course project starts from [PL/OS](https://github.com/plum-umd/plos-risc), a research
prototype of an operating system organized around processes and message passing. We will
explore implementing all or parts of this system for a RISC architecture and proving
properties about the resulting code.

# An Operating System Built Around Communication

An operating system manages computation and mediates access to resources. PL/OS explores a
design in which processes have private state and interact through explicit communication
channels. Its central operations are creating a channel, spawning a process, and synchronizing
with another process to exchange a message.

Communication follows the style of Concurrent ML (CML). A send and a receive meet in a
_rendezvous_: the communication commits when both participants are ready. A sender cannot
simply deposit a message and continue as if the channel were an asynchronous mailbox.
Until a matching operation is available, the process waits.

For example, a parent can create a channel, spawn a child that sends 42 on it, receive that
value, and return 43. Depending on scheduling, either participant might reach the channel
first. The kernel arranges the rendezvous and resumes both processes once the exchange commits.
The prototype includes an executable test of this example.

Programs can also describe a choice between communication events, such as receiving from
either of two channels. Exactly one alternative commits; the other alternatives are withdrawn.
This makes communication itself a synchronization mechanism and gives us precise questions
to ask about the implementation: can an event commit twice? Can a canceled alternative
still be consumed? Does a message reach the intended receiver?

# The Main Pieces

The current prototype brings several layers together in Lean:

- A small source language with functions, local bindings, channel creation, process spawning,
  and communication events. An interpreter executes programs in bounded slices.
- A kernel that tracks processes, schedules runnable work, matches communication partners,
  and resumes waiting computations.
- Per-process channel-handle tables. A process uses local handles, and the kernel checks
  and translates them when servicing requests or transferring channels.
- Formal specifications and proofs relating executable behavior to permitted abstract steps.

The design distinguishes a process from the mechanism that protects its state. A process
describes an independent computation; a protection domain enforces a boundary around code
and memory. The project's Wasm design explores separate instances for untrusted code and
shared domains for code satisfying a trusted-code contract. Those are implementation goals
with their own proof obligations. Private state in an abstract model does not by itself
establish isolation in a running machine.

Today, PL/OS is a Lean-hosted process/channel runtime. The repository contains executable
examples, tests, and refinement and invariant proofs for the source implementation. It also
contains Wasm integration work. These results provide a starting point; they do not establish
correctness of a complete operating system running on RISC hardware.

# Our Goal: Implementing the System for RISC

We will use this prototype as a specification, reference implementation, and source of
verification problems. Our goal is to implement all or selected parts of the system for
a RISC architecture, while proving meaningful properties about the code we write.
The scope can range from one carefully verified component to a larger runtime assembled
from several such components.

A useful starting point is the kernel's replaceable storage components: its runnable queue,
process store, waiting communication offers, and channel-handle tables. These have explicit
interfaces and mathematical contracts. For example, a concrete queue implementation must
represent a sequence of runnable process identifiers and implement the required enqueue,
dequeue, and removal behavior.

Moving such a component to RISC code makes representation choices explicit. Where are records
stored? How are pointers and indices represented? What bounds apply to buffers? What happens
on allocation failure? Which registers and memory locations may a routine change?
The code and its specification must agree on these details.

Larger projects could tackle scheduling, rendezvous, or the boundary between running a process
and returning control to the kernel. Interrupt handling, context switching, and hardware
protection introduce additional obligations if they enter our chosen scope. We will make
the target machine, execution model, and assumptions explicit as we develop these projects.

# What Will We Verify?

The properties will depend on the component. Representative goals include:

- Functional correctness: a RISC queue routine implements the specified queue operation.
- Memory safety: a routine accesses only the memory permitted by its preconditions and
  preserves unrelated memory.
- Kernel invariants: runnable entries identify appropriate processes, and waiting offers
  agree with the processes that own them.
- Communication correctness: a rendezvous transfers the intended value, resumes the right
  participants, and retires all losing alternatives.
- Authority preservation: an operation cannot manufacture access to a channel that the
  process has no right to use.

The connection between levels is crucial. We want a relation explaining how registers and
memory represent an abstract component state, and a proof that executing a routine implements
the corresponding abstract operation. The existing component contracts and replacement
proofs give us a route toward reusing higher-level guarantees once those obligations are met.
A machine routine that can fault or suspend also needs an execution contract describing
those outcomes; implementing the right input/output function alone is insufficient.

We will use coding and proof agents to help construct implementations, discover lemmas,
and develop proofs, with Lean checking the formal results. Our responsibility is to choose
the right specifications and ensure that the checked claims concern the code we intend to
run. A successful project will pair working systems code with a clear account of what has
been proved, under which assumptions, and what remains outside the claim.
