import VersoBlog

open Verso Genre Blog

#doc (Post) "Getting Started with Coding Agents" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

Choose a coding agent, connect it to a project, and try a small programming and proof task.

# Choosing a Tool

You are free to choose the tools you use in this course. Claude Code, OpenAI Codex, and
Google's Gemini CLI are three options to explore. Other coding agents are welcome too.
The important capabilities are reading a project, editing files, running its build tools,
and using compiler feedback to revise an attempt.

We hope to provide tokens for Google's Gemini tool to support your course work. This is
not yet confirmed; we will share access and setup details when they are available.

A coding agent works with your actual development environment. It can inspect definitions,
search for lemmas, make changes across files, and invoke Lean. You can ask it to explain code,
investigate an error, or carry out a focused task. You should still read and understand what
it produces.

## Claude Code

[Claude Code](https://code.claude.com/docs/en/quickstart) is Anthropic's coding agent.
Follow the official quickstart to install it for your operating system and set up an account
or another supported authentication method. Once installed, open a terminal in your project
directory and run `claude`; follow the sign-in prompts on your first run.

The quickstart also links to editor and desktop interfaces if you prefer those to a terminal.
Check the access requirements for your chosen account before committing to a paid plan.

## Codex

[Codex](https://developers.openai.com/codex/cli) is OpenAI's coding agent.
Follow the official CLI guide to install it, open a terminal in your project directory, and
run `codex`. On the first run, sign in with ChatGPT or another available sign-in method.
Consult the guide for installation and authentication options that fit your environment.

## Gemini CLI

[Gemini CLI](https://geminicli.com/docs/get-started/) is Google's terminal-based agent.
Its getting-started guide covers installation, authentication, and a first session. With
Node.js and npm installed at the versions required by the guide, install the CLI using
`npm install -g @google/gemini-cli`, then run `gemini` from your project directory.

Follow the authentication prompts. Google account sign-in is one option; consult the
[authentication guide](https://geminicli.com/docs/get-started/authentication/) for account
requirements and alternatives. Any course-provided access may require a different setup;
we will provide those instructions if the hoped-for tokens become available.

# A First Session

First, set up Lean using [Getting Started with Lean](notes/2026-11-7-getting-started-with-lean/).
Use a small practice project and make sure `lake build` succeeds before asking an agent to
change it. Save a Git checkpoint so you can inspect or undo its changes.

Start your agent in that project's directory. Begin with an explanation request:

> Read this project and explain its structure, the Lean version it uses, and how to build it.
> Do not edit any files yet.

Then give it a small task with a clear success condition:

> In a new Lean file, define a function that doubles a natural number and prove that its
> result is even. Use the project's existing toolchain and dependencies. Do not use sorry
> or introduce axioms. Run Lean to check the file, and explain the proof and how you checked it.

Inspect the resulting file in your editor. Ask about any definition, tactic, or library lemma
you do not understand. Run the check yourself and inspect `git diff` before keeping the change.
If the file is not imported by a build target, `lake build` alone may not check it;
use `lake env lean path/to/YourFile.lean` from the project root to check that file directly.

# Working Effectively with an Agent

Give the agent the relevant files, your intended behavior, and a concrete way to check its
work. For a larger task, ask for a plan first and work in small steps. When an attempt fails,
have it inspect the actual compiler output rather than guess what went wrong.

For proof tasks, review the statement separately from the proof. An agent should preserve
the definitions and specification you intended: weakening a conclusion, adding an assumption,
or changing the program can make a theorem easier while losing the property you wanted.
Require completed proofs without `sorry` or unapproved axioms, and review their dependencies.
Lean checking a proof establishes its formal claim; deciding whether that claim captures the
requirement remains part of your work.

Read proposed commands and permission requests before approving them. Keep credentials out
of source files and prompts, and check usage limits or billing settings for your account.
As you gain experience, compare tools on the same small task: how well do they find relevant
lemmas, respond to Lean's errors, preserve your specification, and explain the result?
