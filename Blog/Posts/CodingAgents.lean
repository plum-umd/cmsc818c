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

# Give the Agent Access to Lean

The [Lean LSP MCP server](https://github.com/oOo0oOo/lean-lsp-mcp) connects an agent to
Lean's language server. LSP means Language Server Protocol; MCP means Model Context Protocol.
This gives the agent access to structured feedback from Lean while it works on your files.

## Set Up the Connection

Follow the server's setup guide: install `uv`, which supplies `uvx`, and build your Lean
project with `lake build`. Install `ripgrep` (`rg`) for local search. The agent and server
need access to the same checkout and its Lean toolchain.

For a local terminal agent, add the server using the command for your tool, from your Lean
project's root directory. Choose one of these alternatives:

Claude Code:

```
claude mcp add lean-lsp -s project uvx lean-lsp-mcp
```

Codex CLI, using the syntax in the
[official MCP guide](https://developers.openai.com/codex/mcp):

```
codex mcp add lean-lsp -- uvx lean-lsp-mcp
```

Gemini CLI, using its [MCP configuration guide](https://geminicli.com/docs/tools/mcp-server/):

```
gemini mcp add --scope project lean-lsp uvx lean-lsp-mcp
```

These configure a local standard-input/output server process. If project discovery selects
the wrong checkout, set `LEAN_PROJECT_PATH` in the server's environment to the absolute
Lean project root. Consult the server guide for platform-specific setup.

Restart or reconnect your agent after configuration. Check its MCP connection status; Codex
and Gemini provide `codex mcp list` and `gemini mcp list`. Then ask it to retrieve diagnostics
and a proof goal from a real Lean file. A configured server is useful only if those calls work.

## Use Lean's Feedback in the Proof Loop

The [tool reference](https://github.com/oOo0oOo/lean-lsp-mcp/blob/main/docs/tools.md)
describes the available operations. Particularly useful tools include:

- `lean_goal`: inspect the hypotheses and goal at a location in a proof.
- `lean_diagnostic_messages`: retrieve compiler errors and warnings for a file.
- `lean_local_search`: find declarations in the local project and dependencies.
- `lean_hover_info`: inspect a declaration's type or documentation.
- `lean_multi_attempt`: try candidate tactics at a proof location.
- `lean_verify`: inspect a theorem's axiom dependencies and scan its source.

Ask for a short feedback loop: inspect the goal, search for an applicable lemma, make a
focused change, and check the resulting diagnostics. For example:

> Use Lean LSP MCP to inspect the goal at the failing tactic in this file. Explain the
> hypotheses and conclusion, search the existing libraries, and try a small proof change.
> Preserve the theorem statement and report the diagnostics after your change.

Search results can suggest a lemma; the project's Lean checker must still accept its use.
An axiom audit complements checking the theorem statement and inspecting the diff.

If the connection fails, check that the project builds, the server can find `uvx` and `lake`,
and it is using the intended checkout. The agent can also check a file with
`lake env lean path/to/YourFile.lean`. Use file-level feedback during editing and run the
project's required build and tests before considering a task complete.

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

## Keep Repository Instructions in Version Control

Record durable project guidance in an instruction file so a new session can recover the
working agreements. Use the exact filename `AGENTS.md` for tools configured to read it.
Include the project layout, build commands, proof restrictions, and what counts as completion.
Keep it short, specific, and consistent with the repository's actual workflow.

Tool support differs:

- [Codex reads AGENTS.md](https://developers.openai.com/codex/guides/agents-md) and supports
  instructions at different directory levels. Place shared guidance at the repository root
  and narrower guidance near the relevant work, following its discovery rules.
- [Claude Code's instruction guide](https://code.claude.com/docs/en/memory) describes when it
  loads `AGENTS.md` or `CLAUDE.md`. If it does not load your shared file directly, a
  `CLAUDE.md` containing `@AGENTS.md` imports it. Check your version and loaded instructions.
- [Gemini CLI uses GEMINI.md](https://geminicli.com/docs/cli/gemini-md/) by default. Its
  `context.fileName` setting can include `AGENTS.md` so you can share the same guidance.

Prefer one maintained source of shared rules over independently edited copies. At the start
of a session, ask the agent which instruction files it loaded and which commands it will use
to check its work. After changing configuration, start a fresh session to verify discovery.

Here is a starting template for a small Lean project. Adapt the commands and paths to your
repository; the template is an example, not a file this post installs:

```
# Project instructions

- Use the Lean version in lean-toolchain and the existing Lake dependencies.
- Read the relevant definitions and specifications before changing a proof.
- Preserve theorem statements and specifications unless the task explicitly changes them.
- Do not use sorry, introduce axioms, or weaken a claim to make a proof pass.
- Use Lean LSP MCP to inspect goals and diagnostics when available.
- Search existing declarations before adding helper lemmas.
- During editing, check the changed file with Lean diagnostics or lake env lean.
- Before finishing, run lake build and the tests documented in README.md.
- Inspect theorem dependencies; report remaining assumptions and validation results.
- Keep changes focused and preserve unrelated work.
```

Instruction files guide behavior; they do not enforce mathematical correctness. Maintain the
build, tests, proof review, and axiom checks as independent evidence. Update stale instructions
when the project changes, and keep temporary task notes separate from durable project rules.

## Make Tasks Small and Reviewable

Give each task a clear boundary and success condition. For example, ask the agent to prove
that a queue operation preserves a stated invariant, naming the file and theorem. Have it
explain an intended intermediate lemma before pursuing a large proof.

Keep Git checkpoints between working stages. Review the diff after each stage and ask the
agent to distinguish changes to implementations, specifications, and proofs. If it keeps
trying the same unsuccessful approach, stop to inspect the current goal and reconsider the
invariant or proof decomposition.

When returning in a new session, provide a short handoff: the objective, relevant files,
completed work, remaining goals, and checks already run. Save useful discoveries in project
documentation. Keep long tool transcripts and obsolete experiments out of instruction files.

Read proposed commands and permission requests before approving them. Keep credentials out
of source files and prompts, and check usage limits or billing settings for your account.
As you gain experience, compare tools on the same small task: how well do they find relevant
lemmas, respond to Lean's errors, preserve your specification, and explain the result?
