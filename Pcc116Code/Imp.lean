import Mathlib.Data.Nat.Defs 
import Mathlib.Tactic.Basic 
import Aesop
import Lean.Elab.Tactic

open Lean Elab Meta

-- literals 

inductive Lit : Type
| INat : ℕ → Lit 

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
| `(imp_lit| true) => mkAppM ``Lit.INat #[mkNatLit 1]
| `(imp_lit| false) => mkAppM ``Lit.INat #[mkNatLit 0]
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

-- environments 

abbrev Value := ℕ 

inductive Result (A : Type) : Type where 
| Ok : A → Result A 
| TypeError : Result A 
| OutOfFuel : Result A  

-- semantics of expressions 

abbrev Env := String → Value 

def emptyEnv : Env := λ _ => 0

def updateEnv : String → Value → Env → Env
| s, v, env => λ s' =>
  if Substring.beq s.toSubstring s'.toSubstring
  then v
  else env s

macro  x:term "|->" v:term ";" s:term  : term => 
  `(updateEnv $x $v $s)

def vlt (n1 n2 : Value) : Value := 
  if Nat.blt n1 n2 then 1 else 0

def vand (n1 n2 : Value) : Value := 
  if Nat.beq n1 0 then 0 else n2 

def vnot (n1 : Value) : Value := 
  if Nat.ble n1 0 then 1 else 0  

def evalBOp : Binop → Value → Value → Value
| Binop.BPlus => λ x y => x + y  
| Binop.BLess => vlt 
| Binop.BAnd => vand  

def evalExp : IExp → Env → Value
| IExp.ELit (Lit.INat l), _ => l 
| IExp.EVar v, env => env v
| IExp.EUn _ e1, env => vnot (evalExp e1 env)
| IExp.BOp op e1 e2, env => 
  (evalBOp op) (evalExp e1 env) (evalExp e2 env)

abbrev Fuel := ℕ

def evalStmt : Fuel → Stmt → Env → Result Env 
| 0 , _ , _ => Result.OutOfFuel
| _ + 1, Stmt.Skip , env => Result.Ok env 
| _ + 1, Stmt.Assign v e, env =>
  Result.Ok (v |-> (evalExp e env) ; env)
| fuel' + 1, Stmt.Seq s1 s2, env => 
  match evalStmt fuel' s1 env with 
  | Result.Ok env1 => evalStmt fuel' s2 env1
  | r => r 
| fuel' + 1, Stmt.If e s1 s2, env => 
  match evalExp e env with 
  | 0 => 
    evalStmt fuel' s2 env 
  | _ + 1 => 
    evalStmt fuel' s1 env 
| fuel' + 1, Stmt.While e s1, env => 
  match evalExp e env with 
  | _ + 1 => 
    match evalStmt fuel' s1 env with 
    | Result.Ok env1 => 
      evalStmt fuel' (Stmt.While e s1) env1
    | r => r 
  | 0 => Result.Ok env 

-- semantics of statements 

inductive Eval : Env → Stmt → Env → Prop
| ESkip : ∀ env, Eval env Stmt.Skip env
| EAssign : ∀ env s e v,
            evalExp e env = v →
            Eval env (Stmt.Assign s e) (s |-> v ; env)
| ESeq : ∀ env env1 env2 s1 s2,
           Eval env s1 env1 →
           Eval env1 s2 env2 →
           Eval env (Stmt.Seq s1 s2) env2
| EIfTrue : ∀ env e s1 s2 env1 n,
            evalExp e env = n + 1 →
            Eval env s1 env1 →
            Eval env (Stmt.If e s1 s2) env1
| EIfFalse : ∀ env e s1 s2 env2,
            evalExp e env = 0 →
            Eval env s2 env2 →
            Eval env (Stmt.If e s1 s2) env2
| EWhileFalse : ∀ env e s1,
            evalExp e env = 0 →
            Eval env (Stmt.While e s1) env
| EWhileTrue : ∀ env env1 env2 e s1 n,
            evalExp e env = n + 1 →
            Eval env s1 env1 →
            Eval env1 (Stmt.While e s1) env2 →
            Eval env (Stmt.While e s1) env2


-- Hoare logic 

def Hoare (P : Env → Prop)(s : Stmt)(Q : Env → Prop) :=
  ∀ (env env' : Env), P env → Eval env s env' → Q env'

macro "{*" P:term " *} " "(" s:term ")" " {* " Q:term " *}" : term =>
  `(Hoare $P $s $Q)

-- rules of Hoare logic 

theorem Skip_rule (P : Env → Prop) 
  : {* P *} (Stmt.Skip) {* P *}:= by 
  intros env env' Hp Hev
  cases Hev 
  exact Hp 

def assertion_sub (s : String) (e : IExp) (P : Env → Prop) : Env → Prop := 
  λ env => P (s |-> (evalExp e env) ; env)

macro P:term "[*" s:term "↦" e:term "*]" : term => 
  `(assertion_sub $s $e $P)

theorem Assign_rule (P : Env → Prop)
  s e :   {* P [* s ↦ e *] *}
            (Stmt.Assign s e) 
          {* P *} := by 
  intros env env' Hp H1
  cases H1
  rw [assertion_sub] at Hp
  rename_i He 
  rw [← He]
  assumption


