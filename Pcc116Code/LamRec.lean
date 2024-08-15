import Mathlib.Tactic.Basic 
import Mathlib.Data.Nat.Defs

-- infrastructure

section DeBruijn
  variable {A : Type}

  inductive In : A → List A → Type where 
  | Here : ∀ x xs, In x (x :: xs)
  | There : ∀ x y ys, In x ys → In x (y :: ys)

end DeBruijn

-- syntax 

inductive Ty : Type where 
| Nat : Ty 
| Arrow : Ty → Ty → Ty 
| Rec : List Ty → Ty 

abbrev Ctx := List Ty 

mutual 

  inductive Fields : Ctx → List Ty → Type where 
  | Nil : ∀ ctx, Fields ctx []
  | Cons : ∀ ctx t ts, Exp ctx t → 
                       Fields ctx ts → 
                       Fields ctx (t :: ts)

  inductive Exp : Ctx → Ty → Type where 
  | Num : ∀ ctx, ℕ → Exp ctx Ty.Nat 
  | Var : ∀ ctx t, In t ctx → Exp ctx t 
  | Abs : ∀ ctx t' t, Exp (t' :: ctx) t → 
                      Exp ctx (Ty.Arrow t' t)
  | App : ∀ ctx t t', Exp ctx (Ty.Arrow t' t) → 
                      Exp ctx t' → 
                      Exp ctx t 
  | MkRec : ∀ ctx ts, Fields ctx ts → 
                      Exp ctx (Ty.Rec ts)
  | AccField : ∀ ctx t ts, Exp ctx (Ty.Rec ts) → 
                           In t ts → 
                           Exp ctx t 

end

-- semantics 

mutual 
  def semTy : Ty → Type 
  | Ty.Nat => ℕ 
  | Ty.Arrow t1 t2 => semTy t1 → semTy t2 
  | Ty.Rec ts => semCtx ts 

  def semCtx : List Ty → Type 
  | [] => Unit 
  | t :: ts => semTy t × semCtx ts 
end 

def lookupVar {ctx t} : In t ctx → semCtx ctx → semTy t
| In.Here _ _, H => by 
  simp [semCtx] at H 
  rcases H with ⟨ H1, _H2 ⟩ 
  exact H1 
| In.There _ _ _ ix, H => by 
  simp [semCtx] at H 
  rcases H with ⟨ _H1, H2 ⟩ 
  exact (lookupVar ix H2) 



mutual
  def evalExp {ctx t} : Exp ctx t → semCtx ctx → semTy t 
  | Exp.Num _ n, _ => n
  | Exp.Var _ _ v, env => lookupVar v env
  | Exp.Abs _ _ _ e, env => by 
    simp [semTy] 
    intros v 
    apply evalExp 
    exact e 
    simp [semCtx]
    constructor <;> assumption
  | Exp.App _ _ _ e1 e2, env => by 
    have H1 : _ := by exact (evalExp e1 env)
    have H2 : _ := by exact (evalExp e2 env)
    simp only [semTy] at H1
    simp only [semTy] at H2 
    exact (H1 H2)
  | Exp.MkRec _ _ fs, env => by 
    simp [semTy] 
    exact (evalFields fs env)
  | Exp.AccField _ _ _ e v, env => by 
    have H1 : _ := by exact (evalExp e env)
    simp [semTy] at H1
    exact (lookupVar v H1)
  termination_by e env => sizeOf e
  decreasing_by 
    all_goals simp_wf
    all_goals omega 

  def evalFields {ctx ts} : Fields ctx ts → semCtx ctx → semCtx ts
  | Fields.Nil _ , _ => Unit.unit
  | Fields.Cons _ _ _ v fs, env => by 
    simp [semCtx] 
    constructor 
    apply (evalExp v env) 
    apply (evalFields fs env)
  termination_by fs env => sizeOf fs
  decreasing_by 
    all_goals simp_wf 
    all_goals omega 
end 
