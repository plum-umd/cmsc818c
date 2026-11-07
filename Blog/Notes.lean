import VersoBlog
import Blog.Posts.Welcome
import Blog.Posts.Background
import Blog.Posts.GettingStarted
import Blog.Posts.CodingAgents
import Blog.Posts.Plos
import Blog.Posts.Warmup
import Blog.Posts.ReadingLean
import Blog.Posts.ProgrammingProving
import Blog.Posts.Specifications
import Blog.Posts.OperationalSemantics
import Blog.Posts.Invariants
import Blog.Posts.AuditingProofs
import Blog.Posts.ExecutableSpecification
import Blog.Posts.RepresentationInvariants
import Blog.Posts.Refinement
import Blog.Posts.TestingProofs
import Blog.Posts.FiniteArithmetic
import Blog.Posts.MachineExecution
import Blog.Posts.MachineRoutines
import Blog.Posts.FrameProperties
import Blog.Posts.ComposingProofs
import Blog.Posts.ProcessesProtection
import Blog.Posts.MessagePassing
import Blog.Posts.ChoiceCancellation
import Blog.Posts.Scheduling
import Blog.Posts.Capabilities
import Blog.Posts.Allocation
import Blog.Posts.ContextSwitching
import Blog.Posts.Isolation
import Blog.Posts.ComponentReplacement
import Blog.Posts.SafetyProgress
import Blog.Posts.Nondeterminism
import Blog.Posts.Failures
import Blog.Posts.ModelsHardware
import Blog.Posts.MaintainingProofs

open Verso Genre Blog

#doc (Page) "Course Notes" =>

This table of contents gives the suggested order for the course notes. Work through the
sections in order and read each section from top to bottom. Pages marked _stub_ reserve
space for planned material; they are not completed lessons. The sequence may evolve as
we develop the course project.

# Getting Oriented

1. [Verified Programming, Lean, and Proof Agents](notes/2026-11-7-verified-programming-lean-and-proof-agents/)
1. [Getting Started with Lean](notes/2026-11-7-getting-started-with-lean/)
1. [Getting Started with Coding Agents](notes/2026-11-7-getting-started-with-coding-agents/)
1. [PL/OS: From a Lean Prototype to Verified RISC Code](notes/2026-11-7-plos-from-a-lean-prototype-to-verified-risc-code/)

# Foundations and Workflow

1. [Reading a Lean Project](notes/2026-11-7-reading-a-lean-project/) — _stub_
1. [Programming and Proving in Lean](notes/2026-11-7-programming-and-proving-in-lean/) — _stub_
1. [What Makes a Good Specification?](notes/2026-11-7-what-makes-a-good-specification/)
1. [Operational Semantics](notes/2026-11-7-operational-semantics/)
1. [Invariants and Induction](notes/2026-11-7-invariants-and-induction/)
1. [Auditing a Proof](notes/2026-11-7-auditing-a-proof/) — _stub_

# Developing the Queue Warm-Up

1. [Warm-Up: A Verified Queue from Semantics to RISC](notes/2026-11-7-warmup-a-verified-queue-from-semantics-to-risc/)
1. [An Executable Specification](notes/2026-11-7-an-executable-specification/)
1. [Representation Invariants](notes/2026-11-7-representation-invariants/)
1. [Refinement and Simulation](notes/2026-11-7-refinement-and-simulation/)
1. [Testing Alongside Proofs](notes/2026-11-7-testing-alongside-proofs/) — _stub_
1. [Finite Arithmetic](notes/2026-11-7-finite-arithmetic/) — _stub_
1. [Machine Execution in Lean](notes/2026-11-7-machine-execution-in-lean/) — _stub_
1. [Verifying a Machine Routine](notes/2026-11-7-verifying-a-machine-routine/) — _stub_
1. [Preserving Unrelated State](notes/2026-11-7-preserving-unrelated-state/) — _stub_
1. [Composing Correctness Proofs](notes/2026-11-7-composing-correctness-proofs/) — _stub_

# Building Toward PL/OS

1. [Processes and Protection Domains](notes/2026-11-7-processes-and-protection-domains/) — _stub_
1. [Synchronous Message Passing](notes/2026-11-7-synchronous-message-passing/) — _stub_
1. [Choice and Cancellation](notes/2026-11-7-choice-and-cancellation/) — _stub_
1. [Scheduling](notes/2026-11-7-scheduling/) — _stub_
1. [Channels as Capabilities](notes/2026-11-7-channels-as-capabilities/) — _stub_
1. [Memory Allocation](notes/2026-11-7-memory-allocation/) — _stub_
1. [Context Switching and Traps](notes/2026-11-7-context-switching-and-traps/) — _stub_
1. [Isolation](notes/2026-11-7-isolation/) — _stub_
1. [Replacing a Verified Component](notes/2026-11-7-replacing-a-verified-component/) — _stub_

# Cross-Cutting Questions

Revisit these throughout the earlier sections: safety and failures when specifying the
queue, nondeterminism when studying semantics and scheduling, and the trust boundary
and proof maintenance as implementations develop. The order below is a final review path.

1. [Safety, Progress, and Termination](notes/2026-11-7-safety-progress-and-termination/) — _stub_
1. [Nondeterminism](notes/2026-11-7-nondeterminism/) — _stub_
1. [Failures as Specified Behavior](notes/2026-11-7-failures-as-specified-behavior/) — _stub_
1. [From a Machine Model to Hardware](notes/2026-11-7-from-a-machine-model-to-hardware/) — _stub_
1. [Maintaining Proofs as Code Changes](notes/2026-11-7-maintaining-proofs-as-code-changes/) — _stub_

# Course Updates

1. [Welcome to CMSC 818C](notes/2026-11-7-welcome-to-cmsc-818c/)
