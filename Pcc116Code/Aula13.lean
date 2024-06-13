-- Aula 13: λ-cálculo tipado simples. 

import Mathlib.Data.Nat.Defs 

-- representing De Bruijn indexes 

inductive UFin : ℕ → Type where 
| Zero : ∀ {n}, UFin (n + 1)
| Succ : ∀ {n}, UFin n → UFin (n + 1)

inductive UTerm : ℕ → Type where 
| UVar : ∀ {n}, UFin n → UTerm n 
| UApp : ∀ {n}, UTerm n → UTerm n → UTerm n 
| ULam : ∀ {n}, UTerm (n + 1) → UTerm n 

-- tipos 

inductive Idx {A : Type}(x : A) : List A → Type where 
| Here : ∀ {xs}, Idx x (x :: xs)
| There : ∀ {ys y}, Idx x ys → Idx x (y :: ys)

def index {A : Type}{x : A}{xs} : Idx x xs → ℕ 
| Idx.Here => 0
| Idx.There idx => (index idx) + 1

inductive Lookup {A : Type}(xs : List A) : ℕ → Type where 
| Inside : ∀ (x : A)(p : Idx x xs), Lookup xs (index p)
| Outside : ∀ (m : ℕ), Lookup xs (m + List.length xs)

def lookup {A : Type} : (xs : List A) → (n : ℕ) → Lookup xs n 
| [] , n => Lookup.Outside n
| x :: _, 0 => Lookup.Inside x Idx.Here 
| _ :: xs, n + 1 => 
  match lookup xs n with 
  | Lookup.Inside y idx => Lookup.Inside y (Idx.There idx)
  | Lookup.Outside m => Lookup.Outside m  

-- type syntax 

inductive Ty : Type where 
| Base : Ty 
| Arr : Ty → Ty → Ty 
deriving Repr 

def eqTy (t t' : Ty) : Decidable (t = t') := 
  match t, t' with 
  | Ty.Base, Ty.Base => Decidable.isTrue rfl 
  | Ty.Arr t1 t2, Ty.Arr t1' t2' => 
    match eqTy t1 t1', eqTy t2 t2' with 
    | Decidable.isTrue rfl, Decidable.isTrue rfl => Decidable.isTrue rfl 
    | Decidable.isTrue p , Decidable.isFalse q => by 
      apply Decidable.isFalse 
      intro H 
      cases H 
      simp at * 
    | Decidable.isFalse p, Decidable.isTrue q => by 
      apply Decidable.isFalse 
      intro H
      cases H 
      simp at * 
    | Decidable.isFalse p, Decidable.isFalse q => by 
      apply Decidable.isFalse 
      intro H 
      cases H 
      simp at * 
  | Ty.Base, Ty.Arr _ _ => by 
    apply Decidable.isFalse 
    intro H
    cases H 
  | Ty.Arr _ _, Ty.Base => by 
    apply Decidable.isFalse 
    intro H ; cases H 

instance : DecidableEq Ty := eqTy  

-- definition of untyped syntax 

inductive Raw : Type where 
| UVar : ℕ → Raw 
| UApp : Raw → Raw → Raw 
| ULam : Ty → Raw → Raw 
deriving Repr 

-- typed syntax 

abbrev Ctx := List Ty 

inductive Term : Ctx → Ty → Type where 
| TVar : ∀ {ctx t}, Idx t ctx → Term ctx t 
| TApp : ∀ {ctx t t'}, Term ctx (Ty.Arr t t') → 
                       Term ctx t → 
                       Term ctx t' 
| TLam : ∀ {ctx t'} t, Term (t :: ctx) t' → 
                       Term ctx (Ty.Arr t t')

def erase {ctx t} : Term ctx t → Raw 
| Term.TVar idx => Raw.UVar (index idx)
| Term.TApp t1 t2 => Raw.UApp (erase t1) (erase t2)
| Term.TLam t t1 => Raw.ULam t (erase t1)

-- certified type checker 

inductive Check (ctx : Ctx) : Raw → Type where 
| Ok : ∀ (t : Ty)(e : Term ctx t), Check ctx (erase e)
| Bad : ∀ {e : Raw}, Check ctx e

def check : ∀ (ctx : Ctx)(e : Raw), Check ctx e
| ctx, Raw.UVar n => 
    match lookup ctx n with 
    | Lookup.Inside t idx => Check.Ok t (Term.TVar idx)
    | Lookup.Outside _ => Check.Bad 
| ctx, Raw.UApp e1 e2 => 
    match check ctx e1, check ctx e2 with 
    | Check.Ok Ty.Base _ , _ => Check.Bad 
    | Check.Ok (Ty.Arr t1 t2) tm1, Check.Ok t1' tm2 =>  
      match decEq t1 t1' with 
      | .isTrue p => by 
        cases p 
        exact (Check.Ok t2 (Term.TApp tm1 tm2))
      | .isFalse _ => Check.Bad 
    | _, _ => Check.Bad
| ctx, Raw.ULam t e1 => 
    match check (t :: ctx) e1 with 
    | Check.Ok t' tm1 => Check.Ok _ (Term.TLam t tm1)
    | Check.Bad => Check.Bad 

-- defining the semantics by embedding it into Lean 

-- 1. interpreting types 

def Ty.asType : Ty → Type 
| Ty.Base => Bool 
| Ty.Arr t1 t2 => t1.asType -> t2.asType 


-- 2. intepreting environments 

def semEnv : Ctx → Type 
| [] => Unit 
| x :: xs => x.asType × semEnv xs 

-- 3. interpreting indexes 

def semIdx {ctx t} : Idx t ctx → semEnv ctx → t.asType 
| Idx.Here, (v, _) => v
| Idx.There idx, (_, env) => semIdx idx env

-- 4. interpreting terms 

def interp {ctx t} : Term ctx t → semEnv ctx → t.asType 
| Term.TVar idx, env => semIdx idx env 
| Term.TApp t1 t2, env => (interp t1 env) (interp t2 env)
| Term.TLam _ t, env => λ v => interp t (v, env) 
