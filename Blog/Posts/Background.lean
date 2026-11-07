import VersoBlog

open Verso Genre Blog

#doc (Post) "Verified Programming, Lean, and Proof Agents" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

What would it take to trust a program written with the help of an AI agent?
Reading the code and running tests are good starting points. For some properties, we can go
further: state precisely what the program must do and construct a machine-checked proof that
it does it. This course explores how that style of development changes when agents can help
write both programs and proofs.

# What Is Verified Programming?

Verified programming brings three things together: an implementation, a specification, and a
proof connecting them. The specification describes the behavior we require. The proof establishes
that the implementation meets that specification under explicit assumptions.

Consider a sorting function. We might require that its output is ordered. That is necessary,
but insufficient: a function that always returns an empty list would satisfy it. We also need
the output to contain exactly the input elements, including their multiplicities. Together,
these requirements describe much more of what we mean by sorting.

A test checks particular executions. A correctness theorem can quantify over every input in
the formal model. The theorem still says only what its statement says. If it specifies ordering
but omits preservation of elements, checking the proof will not repair the specification.

Specifications can express different kinds of requirements:

- Functional correctness: a result agrees with a mathematical definition.
- Memory safety: execution does not access memory outside the permitted regions.
- Security: an operation preserves an access-control or information-flow policy.
- Refinement: a concrete implementation behaves according to an abstract model.
- Progress: a system eventually completes an operation, under stated scheduling assumptions.

These are separate properties. A memory-safe program can compute the wrong answer; a functionally
correct implementation can leak secrets through timing. We must choose the claims that matter
and make the relevant model explicit.

For systems software, this often means modeling machine integers, heaps, failures, or concurrent
execution. A proof about unbounded natural numbers does not automatically establish a claim
about overflowing machine arithmetic. A proof about sequential executions does not automatically
cover interference from another thread.

# Success Stories

Formal verification already supports substantial software. The examples below use different
tools and address different parts of the software stack.

## CompCert: Preserving Meaning During Compilation

[CompCert](https://compcert.org/doc/) is an optimizing compiler for a large subset of C,
developed with machine-checked proofs in Rocq. Its correctness results relate
the behavior of source programs to the generated assembly.

This addresses a crucial gap: reasoning about a source program is useful only if compilation
preserves the relevant behavior. It does not make an incorrect C program correct, nor does it
make undefined behavior harmless. The source-language semantics and the theorem's hypotheses
remain part of the claim.

## seL4: Verifying an Operating-System Microkernel

[seL4](https://sel4.systems/Verification/proofs) has machine-checked proofs connecting its
kernel implementation to a specification, using Isabelle/HOL. Its proof stack also includes
security and binary-correctness results for supported configurations.

The scope matters: properties vary by architecture and configuration, and the proof has
assumptions about the underlying machine and environment. Verifying a microkernel also does not
verify every application running above it. See the project's
[verified configurations](https://docs.sel4.systems/projects/sel4/verified-configurations.html)
for the boundaries of the results.

## Verified Cryptography in Widely Used Software

[Project Everest](https://project-everest.github.io/) developed verified cryptographic components
using F\* and related tools. HACL\* verifies properties including memory safety, functional
correctness, and secret independence in its model. Mozilla describes deploying verified
cryptographic implementations in
[Firefox's cryptography library](https://blog.mozilla.org/security/2020/07/06/performance-improvements-via-formally-verified-cryptography-in-firefox/).

These examples show that proofs can accompany code with practical performance and deployment
requirements. They also show why verification is engineering work: selecting abstractions,
connecting models to implementations, and maintaining proofs as code changes all take effort.

# What Is Lean?

[Lean](https://lean-lang.org/functional_programming_in_lean/Introduction/) is both a programming
language and an interactive theorem prover. Lean 4 supports functional programming, executable
programs, and metaprogramming. Its dependent type theory also lets types describe propositions
and lets terms serve as proofs of those propositions.

In ordinary programming, a type might tell us that a function returns a natural number.
A theorem can say something more specific about the returned number. For example:

```leanInit background
```

```lean background
def twice (n : Nat) : Nat := n + n

theorem twice_even (n : Nat) : ∃ k : Nat, twice n = 2 * k := by
  exact ⟨n, (Nat.two_mul n).symm⟩
```

The definition describes a computation. The theorem says that for every natural number input,
the result is twice some natural number. The proof supplies the input itself as the witness
and uses an arithmetic identity to justify the equality.

This theorem is deliberately small. It establishes evenness over Lean's natural numbers, not
an absence of overflow in an arbitrary machine representation. More interesting specifications
will require richer definitions and more substantial proofs.

Lean's interactive tools display the current goal and available hypotheses as we construct
a proof. Tactics automate proof construction: they can simplify expressions, apply lemmas,
or discharge classes of arithmetic goals. The resulting proof terms are checked by Lean's
kernel, a comparatively small implementation of its core type theory. The
[Lean reference manual](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
describes this separation between elaboration, tactics, and kernel checking.

## What Is Lean Being Used For?

Lean supports several overlapping communities:

- Mathematical formalization. [Mathlib](https://github.com/leanprover-community/mathlib4)
  is a community library of definitions, theorems, and proof automation across many areas of
  mathematics. It lets new developments build on existing formal results.
- Software specification and verification. The
  [Cedar specification repository](https://github.com/cedar-policy/cedar-spec) contains a formal
  model and proofs for the Cedar authorization language, together with differential-testing
  infrastructure. This illustrates a useful distinction: proving properties of a model and
  testing an implementation against that model are complementary activities.
- Verification of programs written in other languages.
  [Aeneas](https://github.com/AeneasVerif/aeneas) translates supported Rust programs into
  functional representations for verification, with Lean among its backends. Such a route
  requires attention to both the translated program and the translation's guarantees.
- AI-assisted theorem proving. Lean provides formal statements, proof states, and a checker
  that can guide proof search.

Lean is not limited to mathematics, and using Lean does not by itself make a program verified.
We still need to formulate and prove the relevant properties. An executable program and a
model of another language also have different connections to the code that ultimately runs.

For installation instructions and suggested reading, see
[Getting Started with Lean](notes/2026-11-7-getting-started-with-lean/).

# Coding Agents and Proof Agents

A coding agent combines a language model with tools and an execution loop. It can inspect a
repository, edit files, invoke a compiler, run tests, examine failures, and revise its work.
The tools and feedback distinguish this workflow from asking a chatbot for a single code
snippet. For a concrete example of this tool-based workflow, see the
[Claude Code use-case guide](https://support.claude.com/en/articles/14553517-claude-code-common-developer-use-cases).

We will use the term _proof agent_ for an agent that helps construct formal proofs. It might
search a library, propose a lemma, inspect a goal, write a tactic script, and revise that script
after Lean rejects it. Some systems specialize in theorem proving; a general coding agent
can also work with Lean when given suitable tools and feedback.

A typical interaction looks like this:

1. A human identifies a desired property and reviews its formal statement.
2. The agent inspects definitions and searches for relevant results.
3. The agent proposes a proof or an intermediate lemma.
4. Lean reports remaining goals or errors, or accepts a proof term.
5. The agent revises its attempt; the human reviews the result and its assumptions.

There is concrete evidence that this combination can solve difficult problems. In 2024,
DeepMind's AlphaProof solved three IMO problems using Lean; combined with AlphaGeometry 2's
solution to a geometry problem, the systems reached a silver-medal-equivalent score. This was
a research result with human formalization and substantial computation, rather than a
demonstration of autonomous systems programming. The
[AlphaProof report](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
describes the setup and its limits.

# Why Is the Combination Promising?

Verified programming offers strong assurances, but obtaining them can be tedious and expensive.
A programmer may know why an implementation is correct and still spend substantial effort
finding library lemmas, supplying intermediate facts, and guiding a prover through routine
steps. Changes to the implementation can require another round of proof repair. This work
has helped keep machine-checked verification out of reach for much of everyday software.

Coding agents have the potential to change the economics of verification dramatically. They can
search for lemmas, explore proof strategies, fill in routine arguments, and repair proofs as code evolves.
If agents can automate much of this work, developers can pursue stronger guarantees with far
less manual effort, while retaining the assurances of a mechanical proof checker.

The separation between finding a proof and checking it makes this possibility especially
exciting. An agent can try an idea, inspect Lean's feedback, and try again. It can make mistakes
along the way: an incorrect argument does not become an accepted proof merely because the
model finds it convincing. The result must satisfy the checker. Once constructed, the proof
is an artifact that can be checked again without repeating the agent's search.

We may well be entering a new golden era of machine-checked software. The prospect is that
proofs become practical for a much wider range of programs, and that maintaining them becomes
a routine part of development. Realizing that prospect will require learning how to combine
human judgment, agent-driven search, and mechanical checking effectively.

In this course, we will explore that interaction in the setting of systems code. Correctness
is especially important here because the rest of the computing stack depends on these
foundations: a mistake in a compiler, runtime, or operating system can undermine everything
built above it. Correctness is also especially challenging here. We must confront the machine's
low-level details, including finite-width arithmetic, memory layout, aliasing, mutable state,
and the relationship between an abstract model and actual execution. These are precisely the
places where strong guarantees are valuable and where help constructing proofs could make
an enormous difference.

Recent vulnerabilities make the stakes concrete. In July 2024, OpenSSH fixed
[regreSSHion, CVE-2024-6387](https://www.openwall.com/lists/oss-security/2024/07/01/3),
a signal-handler race in its server. The
[OpenSSH release notes](https://www.openssh.org/txt/release-9.8) describe the possibility of
remote code execution with root privileges and demonstrated exploitation on 32-bit Linux/glibc
systems. A service responsible for secure remote access could itself become the entry point
for taking over a machine. Reasoning about the main execution path alone is insufficient when
a signal can interrupt it and invoke code that is unsafe in that context.

In June 2025, a different kind of boundary failed in
[sudo, CVE-2025-32463](https://access.redhat.com/security/cve/cve-2025-32463).
Its handling of a user-selected root directory could cause the privileged process to load an
attacker-controlled shared library, allowing a local user to obtain root privileges on affected
systems even without authorization in the sudoers policy. Here the issue was the interaction
between privileged execution, filesystem interpretation, and library loading. Memory safety
alone would not establish the intended authorization guarantee.

In April 2026, the Linux kernel's
[Copy Fail vulnerability, CVE-2026-31431](https://ubuntu.com/security/CVE-2026-31431)
exposed another subtle interaction. Incorrect handling of in-place cryptographic operations
in the `algif_aead` module allowed local privilege escalation and potentially container escape.
The [discoverers describe](https://theori.io/news/b4f3a408-ed43-441e-844d-4e59259e5a7b)
modification of the page cache, the memory used to hold file contents. This connects directly
to the challenge of reasoning about aliases and shared state: an operation on one view of
memory must not silently modify data that the caller has no authority to change.

These failures occurred in foundational software that many other programs rely on. They point
toward concrete verification goals: signal handlers must respect the operations permitted in
their execution context, privileged code must preserve authorization boundaries, and memory
updates must respect ownership and permissions. Establishing such properties requires models
that capture the relevant interactions. This is where agents could help us pursue proofs that
would otherwise be prohibitively laborious, and where mechanical checking can make the
resulting assurances stronger than confidence in an agent's generated code.

However, an accepted build is not a complete review. Lean supports placeholders such as `sorry`
and declarations of axioms. A proof can depend on either, including through imported results.
Some computational proof mechanisms also enlarge the trusted base beyond kernel reduction.
Lean's guide to
[validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains these distinctions. We need to inspect theorem statements and dependencies, exclude
unfinished proofs, and agree on permitted assumptions.

An agent must also preserve the question we meant to ask. Strengthening a theorem's preconditions,
weakening its conclusion, changing a definition, or assuming the desired result may make a task easier
while destroying its purpose. Specifications deserve review independently of their proofs.

Our task is to turn this opportunity into working systems: develop executable artifacts,
state meaningful correctness claims, and use agents to construct proofs that survive independent
checking. Along the way, we will investigate which parts of verification agents can automate,
which decisions require human insight, and how to organize development so that the guarantees
remain clear as the code and its proofs grow.
