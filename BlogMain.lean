import VersoBlog
import Blog

open Verso Genre Blog Site Syntax

def courseSite : Site := site Blog.FrontPage /
  "about" Blog.About
  "projects" Blog.Projects /
    "allocator" Blog.Projects.Allocator
    "queue" Blog.Projects.Queue
    "machine" Blog.Projects.Machine
    "compiler" Blog.Projects.Compiler
    "protection" Blog.Projects.Protection
    "scheduler" Blog.Projects.Scheduler
    "risc-lookup" Blog.Projects.RiscLookup
    "risc-handles" Blog.Projects.RiscHandles
  "notes" Blog.Notes with
    Blog.Posts.Background
    Blog.Posts.GettingStarted
    Blog.Posts.CodingAgents
    Blog.Posts.Plos
    Blog.Posts.Warmup
    Blog.Posts.ReadingLean
    Blog.Posts.ProgrammingProving
    Blog.Posts.Specifications
    Blog.Posts.OperationalSemantics
    Blog.Posts.Invariants
    Blog.Posts.AuditingProofs
    Blog.Posts.ExecutableSpecification
    Blog.Posts.RepresentationInvariants
    Blog.Posts.Refinement
    Blog.Posts.TestingProofs
    Blog.Posts.FiniteArithmetic
    Blog.Posts.MachineExecution
    Blog.Posts.MachineRoutines
    Blog.Posts.FrameProperties
    Blog.Posts.ComposingProofs
    Blog.Posts.ProcessesProtection
    Blog.Posts.MessagePassing
    Blog.Posts.ChoiceCancellation
    Blog.Posts.Scheduling
    Blog.Posts.Capabilities
    Blog.Posts.Allocation
    Blog.Posts.ContextSwitching
    Blog.Posts.Isolation
    Blog.Posts.ComponentReplacement
    Blog.Posts.SafetyProgress
    Blog.Posts.Nondeterminism
    Blog.Posts.Failures
    Blog.Posts.ModelsHardware
    Blog.Posts.MaintainingProofs
    Blog.Posts.Welcome

def courseTheme : Theme :=
  { Theme.default with
    primaryTemplate := do
      -- The notes page supplies its own grouped reading order.
      let page ← withReader (fun ctx =>
        if ctx.path.toList == ["notes"] then
          { ctx with params := ctx.params.erase "posts" }
        else ctx) Theme.Default.primary
      let navigation ← Theme.topNav (some "Home")
      pure <| page.visitM (m := Id) (tag := fun tag attrs _ =>
        pure <| if tag == "div" &&
            (attrs.contains ("class", "authors") || attrs.contains ("class", "date")) then
          some .empty
        else if tag == "nav" && attrs.contains ("class", "top") then
          some navigation
        else none) }

def main := blogMain courseTheme courseSite
