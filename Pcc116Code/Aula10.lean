-- Aula 10: Metaprogramação e automação de provas  

import Mathlib.Tactic.Basic 
import Mathlib.Data.Nat.Defs 
import Aesop 
import Lean.Elab.Tactic

-- tactic combinators

inductive Even : ℕ → Prop where 
| zero : Even 0
| succ : ∀ {n}, Even n → Even (n + 2)


-- repeat' and first combinators
-- repeat' t  

lemma repeat'_example1 : Even 4 ∧ Even 10 ∧ Even 20 ∧ Even 50 := by 
  repeat' apply And.intro
  repeat' first 
          | apply Even.succ 
          | apply Even.zero

-- constructor: use a constructor of an inductive type.
-- If more than one is possible, the choice follows textual order. 

lemma repeat'_example2 : Even 4 ∧ Even 10 ∧ Even 20 ∧ Even 50 := by 
  repeat' apply And.intro 
  repeat' constructor 

-- all_goals: apply a tactic in all goals generated.

lemma repeat'_example3 : Even 4 ∧ Even 10 ∧ Even 20 ∧ Even 50 := by 
  repeat' apply And.intro 
  all_goals (repeat' constructor)

-- simple custom tactic defined by a macro 

macro "intro_and_even" : tactic => 
  `(tactic| 
     (repeat' apply And.intro 
      any_goals 
        solve 
        | repeat' 
           first 
            | apply Even.succ 
            | apply Even.zero))

lemma repeat'_example4 : Even 4 ∧ Even 10 ∧ Even 20 ∧ Even 50 := by
  intro_and_even 

-- Metaprogramming monads
-- 
-- Lean supports two different monads for metaprogramming: 
-- 
-- MetaM monad supports: 
-- * it is a state monad providing access to the global context
-- notations and attributes.
-- * it is a option monad, since some its computations may fail.
-- * supports logging using logInfo function

-- TacticM monad extends MetaM with functionalities to work with 
-- goals. 


-- Example: using logging to display some info. 

open Lean Elab Tactic Meta

elab "trace_goals" : tactic => 
  do 
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with 
    | [] => return 
    | _ :: _ => 
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"


lemma even_example5 : Even 30 ∧ Even 16 := by 
  apply And.intro 
  trace_goals 
  intro_and_even 

-- Example: hypothesis tactic 

elab "hypothesis" : tactic =>
  -- ensure the focus on the current goal 
  withMainContext (
    do 
      -- get current goal 
      let target ← getMainTarget
      -- get current local context 
      let lctx ← getLCtx
      for ldecl in lctx do 
        -- implementation detail: hypothesis inserted by Lean. 
        if ! LocalDecl.isImplementationDetail ldecl then 
           -- test equality up to computation 
           let eq ← isDefEq (LocalDecl.type ldecl) target 
           if eq then 
              let goal ← getMainGoal
              -- instantiate the goal with current hypothesis
              MVarId.assign goal (LocalDecl.toExpr ldecl)
              return
      failure)

lemma even_hyp (h : Even 100) : Even 100 := by 
  hypothesis

-- example: creating a DSL using metaprogramming

-- literals 

inductive Lit : Type
| INat : ℕ → Lit 
| IBool : Bool → Lit 

-- operators 

inductive Unop : Type 
| Unot : Unop

inductive Binop : Type 
| BPlus : Binop 
| BAnd  : Binop 
| BLess : Binop 

-- expressions 

inductive IExp : Type 
| ELit : Lit → IExp 
| EVar : String → IExp 
| EUn : Unop → IExp → IExp 
| BOp : Binop → IExp → IExp → IExp 

-- programs 

inductive Stmt : Type 
| Skip : Stmt 
| Assign : String → IExp → Stmt 
| Seq : Stmt → Stmt → Stmt 
| If : IExp → Stmt → Stmt → Stmt 
| While : IExp → Stmt → Stmt 

-- elaborating syntax using macros 

declare_syntax_cat imp_lit

syntax num : imp_lit
syntax "true" : imp_lit
syntax "false" : imp_lit

def elabLit : Syntax → MetaM Expr 
| `(imp_lit| $n:num) => mkAppM ``Lit.INat #[mkNatLit n.getNat]
| `(imp_lit| true) => mkAppM ``Lit.IBool #[.const ``Bool.true []]
| `(imp_lit| false) => mkAppM ``Lit.IBool #[.const ``Bool.false []]
| _ => throwUnsupportedSyntax

elab "test_elabLit" l:imp_lit : term => elabLit l

#reduce test_elabLit 3 
#reduce test_elabLit true 

declare_syntax_cat imp_unop

syntax "not" : imp_unop 

def elabUnop : Syntax → MetaM Expr 
| `(imp_unop| not) => return .const ``Unop.Unot []
| _ => throwUnsupportedSyntax

declare_syntax_cat imp_bin_op 

syntax "+" : imp_bin_op
syntax "and" : imp_bin_op
syntax "<" : imp_bin_op

def elabBinop : Syntax → MetaM Expr 
| `(imp_bin_op| +) => return .const ``Binop.BPlus []
| `(imp_bin_op| and) => return .const ``Binop.BAnd []
| `(imp_bin_op| <) => return .const ``Binop.BLess []
| _ => throwUnsupportedSyntax

-- elaborating expressions 

declare_syntax_cat imp_exp 

syntax imp_lit : imp_exp 
syntax ident : imp_exp 
syntax imp_unop imp_exp : imp_exp 
syntax imp_exp imp_bin_op imp_exp : imp_exp 

syntax "(" imp_exp ")" : imp_exp 

partial def elabExp : Syntax → MetaM Expr 
| `(imp_exp| $l:imp_lit) => do 
  let l ← elabLit l 
  mkAppM ``IExp.ELit #[l] 
| `(imp_exp| $i:ident) => 
  mkAppM ``IExp.EVar #[mkStrLit i.getId.toString]
| `(imp_exp| $b:imp_unop $e:imp_exp) => do 
  let b ← elabUnop b 
  let e ← elabExp e 
  mkAppM ``IExp.EUn #[b,e]
| `(imp_exp| $l:imp_exp $b:imp_bin_op $r:imp_exp) => do 
  let l ← elabExp l 
  let b ← elabBinop b 
  let r ← elabExp r 
  mkAppM ``IExp.BOp #[b, l, r]
| `(imp_exp| ($e:imp_exp)) => 
  elabExp e
| _ => throwUnsupportedSyntax 

elab "test_elabExp" e:imp_exp : term => elabExp e 

#reduce test_elabExp a + 3

-- statements 

declare_syntax_cat imp_stmt 

syntax "skip" : imp_stmt 
syntax ident ":=" imp_exp : imp_stmt 
syntax imp_stmt ";;" imp_stmt : imp_stmt 
syntax "if" imp_exp "then" imp_stmt "else" imp_stmt "fi" : imp_stmt 
syntax "while" imp_exp "do" imp_stmt "od" : imp_stmt 

partial def elabStmt : Syntax → MetaM Expr 
| `(imp_stmt| skip) => return .const ``Stmt.Skip []
| `(imp_stmt| $i:ident := $e:imp_exp) => do 
  let i : Expr := mkStrLit i.getId.toString
  let e ← elabExp e 
  mkAppM ``Stmt.Assign #[i, e]
| `(imp_stmt| $s1:imp_stmt ;; $s2:imp_stmt) => do 
  let s1 ← elabStmt s1 
  let s2 ← elabStmt s2 
  mkAppM ``Stmt.Seq #[s1, s2]
| `(imp_stmt| if $e:imp_exp then $s1:imp_stmt else $s2:imp_stmt fi) => do 
  let e ← elabExp e 
  let s1 ← elabStmt s1 
  let s2 ← elabStmt s2 
  mkAppM ``Stmt.If #[e,s1,s2]
| `(imp_stmt| while $e:imp_exp do $s:imp_stmt od) => do 
  let e ← elabExp e 
  let s ← elabStmt s 
  mkAppM ``Stmt.While #[e, s]
| _ => throwUnsupportedSyntax

elab "{imp|" p: imp_stmt "}" : term => elabStmt p

#reduce {imp|
  a := 5 ;; 
  if a < 3 and a < 1 then 
    c := 5
  else 
    skip 
  fi ;;  
  d := c + 3  
}

-- Exercício: Represente a linguagem de 
-- comandos simples apresentada na aula 09 
-- utilizando macros para construção automática
-- de programas desta linguagem.
