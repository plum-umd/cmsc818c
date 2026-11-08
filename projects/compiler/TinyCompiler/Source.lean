import MiniRisc.Model

namespace Course.TinyCompiler

open Course.MiniRisc

-- ANCHOR: sourceLanguage
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
-- ANCHOR_END: sourceLanguage

-- ANCHOR: sourceSemantics
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
-- ANCHOR_END: sourceSemantics

theorem eval_sound (statement : Stmt) (store : Store) :
    Eval statement store (eval statement store) := by
  induction statement generalizing store with
  | skip => exact Eval.skip
  | assign v expression => exact Eval.assign
  | seq first second firstIH secondIH => exact Eval.seq (firstIH store) (secondIH _)
  | ifzero test yes no yesIH noIH =>
      unfold eval
      split
      · rename_i zero
        exact Eval.zero zero (yesIH store)
      · rename_i nonzero
        exact Eval.nonzero nonzero (noIH store)

end Course.TinyCompiler
