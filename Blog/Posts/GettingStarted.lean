import VersoBlog

open Verso Genre Blog

#doc (Post) "Getting Started with Lean" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

Install Lean and find resources for learning to program and prove with it.

# Installing Lean

The recommended starting point is the
[official installation guide](https://lean-lang.org/install/), which covers Windows, macOS,
and Linux through VS Code and the official Lean 4 extension:

1. Install VS Code and the Lean 4 extension, published by leanprover.
2. Open the extension's setup guide and follow its prompts to install Lean and prerequisites.
3. Open a Lean project folder in VS Code so the extension can use the project's toolchain.

Three names are useful to recognize. Lean is the language, compiler, and prover. Elan manages
Lean toolchain versions. Lake builds projects and manages their dependencies. A project's
`lean-toolchain` file selects its Lean version; use that version when working on the project.

For a first experiment, use the extension's standalone-project command described in
the [getting-started guide](https://lean-lang.org/getting-started/). Try the program and proof in the
[background post](notes/2026-11-7-verified-programming-lean-and-proof-agents/) in a Lean file
and inspect the proof state. The
[manual installation guide](https://lean-lang.org/install/manual/) provides command-line
alternatives if the recommended setup does not fit your environment.

# Resources for Learning Lean

For this course, start with programming and basic proof construction, then consult the other
resources as needed:

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
  introduces Lean as a programming language, including data types, recursion, monads, dependent
  types, and the relationship between programs and proofs. This is a good starting point for
  programmers coming to Lean.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
  develops the foundations of proof writing: propositions, quantifiers, equality, tactics,
  inductive types, and induction. Work through examples in the editor to see how goals change.
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  teaches proof writing through mathematical examples using Mathlib. It is useful for learning
  how to apply existing lemmas and work within a substantial formal library.
- [The Lean Language Reference](https://lean-lang.org/doc/reference/latest/)
  gives detailed descriptions of the language, tactics, and tools. Use it to look up a feature
  as you encounter it; the books above provide a more gradual introduction.

When running a resource's examples, follow its project setup and toolchain instructions.
Different books and projects may target different Lean releases.
