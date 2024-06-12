-- Aula 14: Formalizando compiladores / semântica de linguagens imperativas

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Finmap
import Aesop 

-- definição de uma linguagem de expressões 

open List 

inductive Expr : Type where 
| EConst : ℕ → Expr 
| EPlus : Expr → Expr → Expr 
| ETimes : Expr → Expr → Expr 
deriving Repr 

-- avaliando expressões

@[simp]
def eval : Expr → ℕ 
| Expr.EConst n => n 
| Expr.EPlus e1 e2 => eval e1 + eval e2 
| Expr.ETimes e1 e2 => eval e1 * eval e2 

-- definição de uma máquina virtual

inductive Instr : Type where 
| IPush : ℕ → Instr 
| IAdd : Instr 
| IMul : Instr 
deriving Repr 

-- semântica da máquina virtual 

abbrev Stack := List ℕ 

@[simp]
def execInstr : Instr → Stack → Stack 
| Instr.IPush n, stk => n :: stk
| Instr.IAdd, v2 :: v1 :: stk => (v1 + v2) :: stk
| Instr.IMul, v2 :: v1 :: stk => (v1 * v2) :: stk
| _ , stk => stk

@[simp]
def interp : List Instr → Stack → Stack 
| [] , stk => stk 
| i :: is, stk => 
  interp is (execInstr i stk)

-- definição do compilador 

@[simp]
def compile : Expr → List Instr 
| Expr.EConst n => [Instr.IPush n]
| Expr.EPlus e1 e2 => compile e2 ++ compile e1 ++ [Instr.IAdd]
| Expr.ETimes e1 e2 => compile e2 ++ compile e1 ++ [Instr.IMul]

-- propriedade fundamental: preservação da semântica
-- resultado produzido pelo código compilado é igual ao do código fonte.

-- Lemma 1. relação da interpretação de instruções e concatenação.

@[simp]
lemma interp_app 
  : ∀ (c c' : List Instr) (stk : Stack), 
      interp (c ++ c') stk = interp c' (interp c stk) := by 
      intros c 
      induction c <;> aesop 

-- Lemma 2. Provando o resultado para uma pilha qualquer.

lemma compile_preserves' 
  : ∀ e stk, interp (compile e) stk = (eval e) :: stk := by 
  intros e 
  induction e <;> aesop (add safe [apply Nat.add_comm, apply Nat.mul_comm]) 

-- teorema final

theorem compile_preserves e 
  : interp (compile e) [] = [eval e] := compile_preserves' e []


-- semântica de uma linguagem imperativa 

-- definição da sintaxe 

inductive Literal : Type where 
| LNat : ℕ → Literal 
| LBool : Bool → Literal 
deriving Repr 

inductive Exp : Type where 
| Lit : Literal → Exp 
| Var : String → Exp 
| Add : Exp → Exp → Exp 
| Lt : Exp → Exp → Exp 
| And : Exp → Exp → Exp 
deriving Repr 

inductive Stmt : Type where 
| Skip : Stmt
| Decl : String → Exp → Stmt 
| Assign : String → Exp → Stmt 
| Seq : Stmt → Stmt → Stmt 
| If : Exp → Stmt → Stmt → Stmt 
deriving Repr 

-- sistema de tipos. 

inductive Ty : Type where 
| TNat | TBool 
deriving Repr

@[simp] 
def Ty.beq : Ty → Ty → Bool 
| Ty.TNat, Ty.TNat => true 
| Ty.TBool, Ty.TBool => true 
| _, _ => false

abbrev Ctx := List (String × Ty)

-- verificando tipo de expressões 

@[simp]
def tcLit : Literal → Ty 
| Literal.LNat _ => Ty.TNat
| Literal.LBool _ => Ty.TBool

@[simp]
def tcExp : Ctx → Exp → Option Ty 
| _, Exp.Lit l => pure (tcLit l)
| ctx, Exp.Var s => ctx.lookup s 
| ctx, Exp.Add e1 e2 => do 
  let t1 ← tcExp ctx e1 
  let t2 ← tcExp ctx e2 
  match t1, t2 with 
  | Ty.TNat, Ty.TNat => pure Ty.TNat 
  | _ , _ => .none 
| ctx, Exp.Lt e1 e2 => do 
  let t1 ← tcExp ctx e1 
  let t2 ← tcExp ctx e2 
  match t1, t2 with 
  | Ty.TNat, Ty.TNat => pure Ty.TBool
  | _ , _ => .none 
| ctx, Exp.And e1 e2 => do 
  let t1 ← tcExp ctx e1 
  let t2 ← tcExp ctx e2 
  match t1, t2 with 
  | Ty.TBool, Ty.TBool => pure Ty.TBool
  | _ , _ => .none

-- verificando tipos de comandos 

-- semântica como definitional interpreter 

abbrev Env := List (String × Literal)

inductive Res (A : Type) where 
| Ok : A → Res A 
| Timeout : Res A 
| TypeError : Res A 
deriving Repr 

def Res.pure {A : Type} : A → Res A := .Ok 

instance : Pure Res where 
  pure := Res.pure 

def Res.bind {A B : Type} : Res A → (A → Res B) → Res B 
| .Ok x, f => f x 
| .Timeout, _ => .Timeout
| .TypeError, _ => .TypeError

instance : Bind Res where 
  bind := Res.bind

-- semântica de expressões 

@[simp]
def evalExp (env : Env) : Exp → Res Literal 
| Exp.Lit l => pure l 
| Exp.Var v => 
  match env.lookup v with 
  | .some l => .Ok l 
  | .none => .TypeError 
| Exp.Add e1 e2 => do 
  let l1 ← evalExp env e1 
  let l2 ← evalExp env e2 
  match l1, l2 with 
  | Literal.LNat n1, Literal.LNat n2 => .Ok (Literal.LNat (n1 + n2))
  | _ , _ => .TypeError 
| Exp.Lt e1 e2 => do 
  let l1 ← evalExp env e1 
  let l2 ← evalExp env e2 
  match l1, l2 with 
  | Literal.LNat n1, Literal.LNat n2 => .Ok (Literal.LBool (n1 < n2))
  | _ , _ => .TypeError
| Exp.And e1 e2 => do 
  let l1 ← evalExp env e1 
  let l2 ← evalExp env e2 
  match l1, l2 with 
  | Literal.LBool b1, Literal.LBool b2 => .Ok (Literal.LBool (b1 && b2))
  | _ , _ => .TypeError

-- semântica de comandos 

-- lemma: type soundness para expressões.

@[simp]
def envAgreeCtx : Env → Ctx → Bool  
| [] , [] => true
| ((s, v) :: env), ((s', t) :: ctx) => 
  s = s' && Ty.beq (tcLit v) t && envAgreeCtx env ctx
| _, _ => false

lemma envAgreeCtxNil : ∀ ctx, envAgreeCtx [] ctx = true → ctx = [] := by 
  intros ctx H1 
  cases ctx with 
  | nil => rfl
  | cons p ps => 
    simp at * 

lemma lookupSound : ∀ env ctx s t, envAgreeCtx env ctx →  
                                   lookup s ctx = .some t → 
                                   ∃ v, lookup s env = .some v ∧ 
                                        tcLit v = t := by
    intros env     
    induction env with 
    | nil => 
      intros ctx s t H1 H2
      apply envAgreeCtxNil at H1 
      rw [H1] at H2
      simp at *
    | cons p env' IH => 
      intros ctx s t H1 H2 
      rcases p with ⟨ s1 , v1 ⟩ 
      sorry 

lemma tyExpSound : ∀ e ctx env t, tcExp ctx e = .some t → 
                                  envAgreeCtx env ctx → 
                    ∃ l, evalExp env e = Res.Ok l ∧ tcLit l = t := by 
  intros e 
  induction e with 
  | Lit l => 
    intros ctx env t H1 H2 
    exists l 
    aesop 
  | Var v =>
    intros ctx env t H1 H2 
    simp at * 
    sorry 
  | Add e1 e2 IH1 IH2 => sorry 
  | And e1 e2 IH1 IH2 => sorry 
  | Lt e1 e2 IH1 IH2 => sorry 


