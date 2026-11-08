import VersoBlog
import TinyCompiler
import TinyCompiler.Examples

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 4: A Small Verified Compiler" =>

A compiler connects two languages. Its correctness claim is that a program's meaning survives
translation, even though its target execution may involve many smaller steps. In this project,
we compile a tiny imperative language into the instruction set from Project 3 and prove that
the resulting machine program implements the source semantics.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/compiler) contains
the source language, compiler, execution examples, and proof obligations. The target-machine
definitions are supplied; completing Project 3's proof exercises is not a prerequisite.

# Build and Explore

From the repository root:

```
cd projects/compiler
lake build
```

The main modules are:

- `TinyCompiler/Source.lean`: source syntax, a big-step semantics, an executable evaluator,
  and a supplied soundness theorem for that evaluator.
- `TinyCompiler/Compile.lean`: the register mapping, code generation, placement checks,
  and definitions used to express code layout and register frames.
- `TinyCompiler/Correctness.lean`: the propositions you will prove.
- `TinyCompiler/Support.lean`: checked register-update and run-composition lemmas.
- `TinyCompiler/Examples.lean` and `Checks.lean`: concrete source and target executions.

The starter compiles and its regression checks pass. The compiler-correctness propositions
are student obligations, not supplied proofs of a verified compiler.

# Specify the Source Language

## Stores, Expressions, and Statements

```anchor sourceLanguage (module := TinyCompiler.Source)
abbrev Variable := Fin 30

structure Store where
  values : Vector Word 30 := Vector.replicate 30 0
  deriving DecidableEq, Repr

def Store.read (store : Store) (v : Variable) : Word := store.values[v.val]

def Store.write (store : Store) (v : Variable) (value : Word) : Store :=
  { values := store.values.set v.val value v.isLt }

inductive Expr where
  | var (v : Variable)
  | literal (value : BitVec 12)
  | add (left right : Variable)
  deriving DecidableEq, Repr

def Expr.eval (expression : Expr) (store : Store) : Word :=
  match expression with
  | .var v => store.read v
  | .literal value => signed value
  | .add left right => store.read left + store.read right

inductive Stmt where
  | skip
  | assign (destination : Variable) (expression : Expr)
  | seq (first second : Stmt)
  | ifzero (test : Variable) (yes no : Stmt)
  deriving DecidableEq, Repr
```

There are 30 source variables, numbered zero through 29. Each holds a 64-bit word.
Expressions read a variable, denote a signed 12-bit literal, or add two variables. Addition
wraps modulo `2^64`, just as it does on the target machine. Literals are sign-extended to
64 bits; larger values may enter through the initial store or be computed by addition.

This is deliberately a small expression language. Addition's operands are variable names,
not arbitrary nested expressions. More complicated calculations can be split into assignments.
That keeps register allocation and spilling out of the initial project while retaining
aliasing cases such as assigning `x + y` back to `x`.

Statements support doing nothing, assignment, sequencing, and a conditional test for zero.
There are no loops in the core language. Every source evaluation terminates structurally,
which lets us state total compiler correctness without introducing divergence yet.

## Source Semantics

```anchor sourceSemantics (module := TinyCompiler.Source)
inductive Eval : Stmt → Store → Store → Prop where
  | skip : Eval .skip store store
  | assign : Eval (.assign v expression) store
      (store.write v (expression.eval store))
  | seq (first : Eval left before middle) (second : Eval right middle after) :
      Eval (.seq left right) before after
  | zero (testZero : before.read test = 0) (body : Eval yes before after) :
      Eval (.ifzero test yes no) before after
  | nonzero (testNonzero : before.read test ≠ 0) (body : Eval no before after) :
      Eval (.ifzero test yes no) before after

def eval (statement : Stmt) (store : Store) : Store :=
  match statement with
  | .skip => store
  | .assign v expression => store.write v (expression.eval store)
  | .seq first second => eval second (eval first store)
  | .ifzero test yes no =>
      if store.read test = 0 then eval yes store else eval no store
```

`Eval statement before after` specifies permitted source executions. Assignment evaluates
the expression in the old store, then updates its destination. Sequencing passes the first
result to the second statement. A conditional evaluates exactly one arm based on the test's
value in the original store.

The function `eval` computes that result. The supplied `eval_sound` theorem connects its
result to `Eval`. You will prove the converse, `Exercises.SourceComplete`, so the evaluator
can serve as a convenient reference without replacing the independently stated semantics.

# Relate Stores to Machine States

```anchor registerMapping (module := TinyCompiler.Compile)
def reg (v : Variable) : Register := ⟨v.val + 1, by omega⟩

def Rep (store : Store) (machine : State) : Prop :=
  ∀ v, machine.readReg (reg v) = store.read v
```

Source variable zero occupies machine register 1; variable 29 occupies register 30.
The zero register is unavailable for source variables, and register 31 is reserved.
The restricted expressions need no scratch register. `Rep` states that every source value
agrees with its assigned architectural register; it does not constrain the PC or register 31.

Prove that the mapping is injective and avoids registers zero and 31. These facts justify
updating one source variable without changing the others. Operands must be read before the
destination is written, including when their registers coincide.

# Lay Out the Compiled Code

```anchor emitter (module := TinyCompiler.Compile)
def emitExpr (destination : Variable) (expression : Expr) : Instruction :=
  match expression with
  | .var v => .add (reg destination) (reg v) 0
  | .literal value => .addi (reg destination) 0 value
  | .add left right => .add (reg destination) (reg left) (reg right)

def emit (statement : Stmt) : List Instruction :=
  match statement with
  | .skip => []
  | .assign destination expression => [emitExpr destination expression]
  | .seq first second => emit first ++ emit second
  | .ifzero test yes no =>
      let yesCode := emit yes
      let noCode := emit no
      [.bne (reg test) 0 (BitVec.ofNat 13 (4 * (yesCode.length + 2)))] ++
        yesCode ++ [.beq 0 0 (BitVec.ofNat 13 (4 * (noCode.length + 1)))] ++ noCode
```

Each assignment emits one instruction. Copying uses addition with the zero register;
literals use `addi`; addition uses `add`. A sequence concatenates the compiled fragments.
`skip` emits no instructions.

The conditional has this layout:

1. A `bne` skips to the else arm when the test is nonzero.
2. The then arm follows the test instruction.
3. An unconditional `beq` skips past the else arm after the then arm finishes.
4. The else arm ends at the conditional's exit address.

Branch offsets count bytes and are relative to the branch instruction itself. The first
offset is four times the then-arm length plus two instruction positions. The second is four
times the else-arm length plus one position. Draw the instruction addresses and justify
both offsets, including the cases where either arm is empty.

# Reject Code That Cannot Be Represented

```anchor checkedCompilation (module := TinyCompiler.Compile)
def maxInstructions : Nat := 1023

inductive CompileError where
  | codeTooLarge
  | misalignedBase
  | addressOverflow
  deriving DecidableEq, Repr

def compile (base : Nat) (statement : Stmt) : Except CompileError Program :=
  let code := emit statement
  if code.length > maxInstructions then .error .codeTooLarge
  else if base % 4 ≠ 0 then .error .misalignedBase
  else if base + 4 * (code.length + 1) > 2 ^ 64 then .error .addressOverflow
  else .ok ⟨base, (code ++ [Instruction.ebreak]).toArray⟩
```

The signed 13-bit branch field can represent positive offsets through 4095 bytes. Since
instructions are four bytes apart, the largest positive aligned offset is 4092. Limiting
the emitted body to 1023 instructions keeps every forward branch within that range.
Proving that the bound also applies to nested substatements is part of the assignment.

`emit` alone converts offsets into finite bitvectors and could truncate an oversized value.
Only `compile` is the checked entry point. It rejects an oversized body, an unaligned base,
or an image crossing the address-space boundary before returning a program for execution.
Prove that accepted code has the intended signed offsets, rather than assuming a bitvector
conversion preserves every natural number.

The complete image appends an `ebreak` at the exit address. Placement checks include that
marker, so the exit is a representable address with a fetchable instruction. It is used by
the test harness to observe completion, not emitted for each substatement.

# State a Compositional Correctness Goal

```anchor codeLayout (module := TinyCompiler.Compile)
def SafeBranches : Stmt → Prop
  | .skip | .assign .. => True
  | .seq first second => SafeBranches first ∧ SafeBranches second
  | .ifzero _ yes no =>
      4 * ((emit yes).length + 2) < 2 ^ 12 ∧
      4 * ((emit no).length + 1) < 2 ^ 12 ∧ SafeBranches yes ∧ SafeBranches no

def CodeAt (code : List Instruction) (address : Nat) (program : Program) : Prop :=
  address % 4 = 0 ∧ address + 4 * code.length < 2 ^ 64 ∧
    ∀ (index : Nat) (inside : index < code.length),
      fetch program (BitVec.ofNat 64 (address + 4 * index)) = .ok code[index]
```

`SafeBranches` records the arithmetic conditions needed for conditional offsets.
`CodeAt code address program` says that the fragment's instructions are fetchable at the
specified addresses, its base is aligned, and its exit address does not wrap.
It does not require the fragment to occupy the whole program.

That distinction is important for sequencing. The first statement's exit may be the second
statement's entry. A theorem requiring a breakpoint immediately after every fragment would
not compose into the intended program.

```anchor localCorrectness (module := TinyCompiler.Correctness)
def LocalCorrect : Prop :=
  ∀ (statement : Stmt) (store : Store) (machine : State) (program : Program) (address : Nat),
    SafeBranches statement → CodeAt (emit statement) address program →
    machine.pc = BitVec.ofNat 64 address → Rep store machine →
      ∃ steps : Nat, steps ≤ (emit statement).length ∧
        let result := run steps program machine
        result.stop = .suspended ∧ result.retired = steps ∧
        result.state.pc = BitVec.ofNat 64 (address + 4 * (emit statement).length) ∧
        Rep (eval statement store) result.state ∧ Frame statement machine result.state
```

Starting from corresponding states, the machine must reach the fragment's exit after a
bounded number of successful steps, with the correct source result and a register frame.
The execution is suspended there because the chosen fuel has just been exhausted. It has
not attempted to fetch the next fragment's instruction.

The witness `steps` may depend on which conditional path executes. It is bounded by emitted
code size but need not equal it. `Frame` requires preservation of every register outside
the statement's possible destinations, including the reserved register. For a conditional,
the footprint conservatively includes destinations from both arms.

The supplied `Support.run_append` theorem joins a suspended execution with a subsequent
execution. Use it to compose instruction runs into statement runs and statement runs into
sequences. The earlier run must suspend; resuming an arbitrary trapped state would not
justify the same composition argument.

# Connect the Compiler Entry Point to the Result

```anchor compilerCorrectness (module := TinyCompiler.Correctness)
def CompilerCorrect : Prop :=
  ∀ (base : Nat) (statement : Stmt) (program : Program) (store : Store) (machine : State),
    compile base statement = .ok program →
    machine.pc = BitVec.ofNat 64 base → Rep store machine →
      let result := run ((emit statement).length + 1) program machine
      result.stop = .trapped .breakpoint ∧
      result.state.pc = BitVec.ofNat 64 (base + 4 * (emit statement).length) ∧
      result.retired ≤ (emit statement).length ∧
      Rep (eval statement store) result.state ∧ Frame statement machine result.state
```

For a program accepted by `compile`, a budget of body length plus one is sufficient to
execute the selected path and attempt the exit breakpoint. The resulting PC must identify
that marker, source and target values must agree, and unrelated registers must be preserved.
An early breakpoint or another fault is not an acceptable substitute for reaching the exit.

Combine placement, local correctness, source-evaluator soundness, and the final breakpoint
step to obtain this theorem. Together with source completeness, it states agreement with
the source relation, not merely agreement between two executable functions.

# Try a Source Program

```anchor sourceExample (module := TinyCompiler.Examples)
def exampleProgram : Stmt :=
  .seq (.assign 0 (.literal 7))
    (.seq (.assign 1 (.literal (BitVec.ofInt 12 (-7))))
      (.seq (.assign 0 (.add 0 1))
        (.ifzero 0 (.assign 2 (.literal 42)) (.assign 2 (.literal 99)))))
```

This program assigns 7 and minus 7, adds them with the result stored back into the first
variable, then selects the zero arm. Variable 2 should finish with 42. The source variable
numbers here are not physical register numbers: variable 2 is represented in register 3.

```leanInit compilerProject
```

```lean compilerProject
open Course.MiniRisc Course.TinyCompiler Course.TinyCompiler.Examples

example : (eval exampleProgram {}).read 2 = 42 := by decide
example : ((runCompiled 0 exampleProgram {}).map (·.state.readReg (reg 2))) = some 42 := by decide
example : ((runCompiled 4096 exampleProgram {}).map (·.stop)) =
    some (.trapped .breakpoint) := by decide
```

`runCompiled` is a convenience for examples: it creates a corresponding initial register
file and runs the accepted image. Your correctness theorem quantifies over *all* initial
machine states satisfying `Rep` and the entry-PC condition, not just states made by this helper.

# Core Assignment

1. *Understand the source specification.* Prove `Exercises.SourceComplete`. Explain why
   assignment reads the old store and why both languages use the same modular arithmetic.
2. *Establish the representation.* Prove `Exercises.RegisterMapping` and the read/write
   facts needed to update a represented variable. Use the supplied machine-register lemmas.
3. *Verify straight-line translation.* Prove local correctness for `skip`, assignment, and
   sequencing. Cover assignments whose destination is also an operand. Use the code placement
   hypothesis and run-composition lemma, rather than assuming an isolated instruction array.
4. *Verify control-flow translation.* Prove `Exercises.LayoutSafe`, then the conditional
   case of `Exercises.LocalCorrect`. Split on the source test, justify the taken target,
   and account for the unconditional jump after the then arm. Both empty arms are allowed.
5. *Verify checked compilation.* Prove `Exercises.Placement` and derive
   `Exercises.CompilerCorrect`. Include termination, the exit address, and the frame property.

Create `TinyCompiler/Solution.lean`, import the supplied modules, and import your solution
from `Checks.lean`. Keep the source semantics, compiler, and exercise propositions fixed.
The source and target interpreters are references for your proofs; passing their examples
alone does not discharge the universal obligations.

Submit the proofs with a short account of the state correspondence and conditional layout.
Explain why the fragment theorem stops before fetching at its exit, why branch offsets need
bounds, and how the machine result implies the source semantics. Include examples for both
conditional arms, aliasing, arithmetic wraparound, and a rejected oversized program.
Inspect theorem assumptions with `#print axioms`, following `Audit.lean`; do not introduce
axioms or proof placeholders. Ask an agent to state the induction hypothesis and layout
conditions before constructing the compiler proof.

# Optional Extensions

1. Change the conditional layout so the nonzero arm falls through. Prove the same semantic
   result with the new offsets and execution bound.
2. Extend expressions with nested addition. Choose a strategy for temporary registers or
   storage, state its resource bound, and prove that it preserves live source variables.
3. Add a restricted countdown loop. Specify its source behavior and reuse a decreasing
   unsigned-counter measure to prove termination. Account for additional instruction costs;
   the loop-free bound by code size will no longer suffice.

General loops, register allocation, spilling, binary instruction encoding, and data memory
remain outside the core project. The goal here is a complete translation argument with
explicit limits, not a large source language.
