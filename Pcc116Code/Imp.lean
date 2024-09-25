import Mathlib.Data.Nat.Defs 
import Mathlib.Tactic.Basic 
import Aesop
import Lean.Elab.Tactic

-- definition of state

namespace ImpState 

  def State : Type := 
    String → ℕ 

  def State.update (name : String)
                   (val : ℕ)
                   (s : State) : State :=
    λ name' => if name' = name then val 
               else s name' 

  macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

  @[simp] 
  theorem update_apply (name : String) 
                       (val : ℕ) 
                       (s : State) 
    : (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

  @[simp] 
  theorem update_apply_neq (name name' : String) 
                           (val : ℕ) (s : State)
                           (hneq : name' ≠ name)
    : (s[name ↦ val]) name' = s name' := by
      apply if_neg
      assumption

  @[simp] 
  theorem update_override (name : String) 
                          (val₁ val₂ : ℕ) 
                          (s : State)
    : s[name ↦ val₂][name ↦ val₁] = s[name ↦ val₁] := by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

  @[simp] 
  theorem update_swap (name₁ name₂ : String) 
                      (val₁ val₂ : ℕ) 
                      (s : State)
                      (hneq : name₁ ≠ name₂) 
    : s[name₂ ↦ val₂][name₁ ↦ val₁] = 
      s[name₁ ↦ val₁][name₂ ↦ val₂] := by
        apply funext
        intro name'
        cases Classical.em (name' = name₁) with
        | inl h => simp [*]
        | inr h =>
           cases Classical.em (name' = name₁) with
           | inl h => simp [*]
           | inr h => simp [State.update, *]

  @[simp] 
  theorem update_id (name : String) (s : State) 
    : s[name ↦ s name] = s := by
      apply funext
      intro name'
      simp [State.update]
      intro heq
      simp [*]

  @[simp] 
  theorem update_same_const (name : String)
                            (val : ℕ) 
    : (fun _ ↦ val)[name ↦ val] = (fun _ ↦ val) := by
    apply funext
    simp [State.update]
end ImpState

namespace ImpSyntax
  open ImpState 

  inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

  infixr:90 "; " => Stmt.seq

end ImpSyntax

namespace ImpSemantics 

  open ImpSyntax ImpState 

  inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

  infix:110 " ⟹ " => BigStep

end ImpSemantics

namespace ImpHoare

  open ImpState ImpSyntax ImpSemantics

  def PartialHoare (P : State → Prop) (S : Stmt)
                   (Q : State → Prop) : Prop :=
      ∀ s t, P s → (S, s) ⟹ t → Q t

  macro "{*" P:term " *} " 
        "(" S:term ")" 
        " {* " Q:term " *}" : term => 
        `(PartialHoare $P $S $Q)

  theorem skip_intro {P} :
    {* P *} (Stmt.skip) {* P *} := by
    intro s t hs hst
    cases hst
    assumption

  theorem assign_intro (P) {x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} 
      (Stmt.assign x a) 
    {* P *} := by
    intro s t P' hst
    cases hst with
    | assign => assumption

  theorem seq_intro {P Q R S T} 
    (hS : {* P *} (S) {* Q *})
    (hT : {* Q *} (T) {* R *}) : 
    {* P *} (S ; T) {* R *} := by
    intro s t hs hst
    cases hst with
    | seq _ _ _ u d hS' hT' =>
      apply hT
      apply hS 
      exact hs 
      assumption 
      assumption 

  theorem if_intro {B P Q S T}
      (hS : {* fun s ↦ P s ∧ B s *} (S) {* Q *})
      (hT : {* fun s ↦ P s ∧ ¬ B s *} (T) {* Q *}) :
    {* P *} (Stmt.ifThenElse B S T) {* Q *} := by
      intro s t hs hst
      cases hst with
      | if_true _ _ _ _ _ hB hS' =>
         apply hS
         exact And.intro hs hB
         assumption
      | if_false _ _ _ _ _ hB hT' =>
         apply hT
         exact And.intro hs hB
         assumption

  theorem while_intro (P) {B S}
    (h : {* fun s ↦ P s ∧ B s *} (S) {* P *}) :
    {* P *} 
      (Stmt.whileDo B S) 
    {* fun s ↦ P s ∧ ¬ B s *} := by
      intro s t hs hst
      generalize ws_eq : (Stmt.whileDo B S, s) = Ss
      rw [ws_eq] at hst
      induction hst generalizing s with
      | skip s'                       => cases ws_eq
      | assign x a s'                 => cases ws_eq
      | seq S T s' t' u hS hT ih      => cases ws_eq
      | if_true B S T s' t' hB hS ih  => cases ws_eq
      | if_false B S T s' t' hB hT ih => cases ws_eq
      | while_true B' S' s' t' u hB' hS hw ih_hS ih_hw =>
        cases ws_eq
        apply ih_hw
        apply h
        apply And.intro <;> assumption
        exact hS 
        rfl 
      | while_false B' S' s' hB'      =>
        cases ws_eq
        aesop

  theorem consequence {P P' Q Q' S}
    (h : {* P *} (S) {* Q *}) 
    (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) : {* P' *} (S) {* Q' *} := by 
    intros s t Hs Hst 
    apply hq 
    apply h 
    apply hp 
    exact Hs 
    exact Hst 

  theorem consequence_left (P') {P Q S}
    (h : {* P *} (S) {* Q *}) 
    (hp : ∀s, P' s → P s) : {* P' *} (S) {* Q *} := by 
    apply consequence <;> try assumption 
    aesop 

theorem consequence_right (Q) {Q' P S}
    (h : {* P *} (S) {* Q *}) 
    (hq : ∀s, Q s → Q' s) : {* P *} (S) {* Q' *} := by 
    apply consequence <;> try assumption 
    aesop 

theorem skip_intro' {P Q} (h : ∀s, P s → Q s) :
  {* P *} (Stmt.skip) {* Q *} := by 
  apply consequence
  apply skip_intro 
  assumption 
  aesop 

theorem assign_intro' {P Q x a}
    (h : ∀s, P s → Q (s[x ↦ a s])):
  {* P *} (Stmt.assign x a) {* Q *} :=
  consequence (assign_intro Q) h (by aesop)

theorem seq_intro' {P Q R S T} 
    (hT : {* Q *} (T) {* R *})
    (hS : {* P *} (S) {* Q *}) :
  {* P *} (S; T) {* R *} := by 
  apply seq_intro 
  exact hS 
  exact hT 

theorem while_intro' {B P Q S} (I)
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s)
    (hQ : ∀s, ¬ B s → I s → Q s) :
  {* P *} (Stmt.whileDo B S) {* Q *} := by 
  apply consequence 
  apply while_intro 
  exact hS 
  exact hP 
  aesop 

theorem assign_intro_forward (P) {x a} :
  {* P *}
    (Stmt.assign x a)
  {* fun s ↦ ∃n₀, P (s[x ↦ n₀]) ∧ s x = a (s[x ↦ n₀]) *} := by
    apply assign_intro'
    intro s hP
    apply Exists.intro (s x)
    simp [*]

theorem assign_intro_backward (Q) {x a} :
  {* fun s ↦ ∃n', Q (s[x ↦ n']) ∧ n' = a s *}
    (Stmt.assign x a)
  {* Q *} := by
    apply assign_intro'
    intro s hP
    cases hP with
    | intro n' hQ => aesop 


  def Stmt.invWhileDo (I B : State → Prop) (S : Stmt) : Stmt :=
    Stmt.whileDo B S

  theorem invWhile_intro {B I Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hQ : ∀s, ¬ B s → I s → Q s) :
    {* I *} (Stmt.invWhileDo I B S) {* Q *} := by 
      apply while_intro' <;> aesop 
      
  theorem invWhile_intro' {B I P Q S}
    (hS : {* fun s ↦ I s ∧ B s *} (S) {* I *})
    (hP : ∀s, P s → I s) (
    hQ : ∀s, ¬ B s → I s → Q s) :
    {* P *} (Stmt.invWhileDo I B S) {* Q *} := by 
      apply while_intro' <;> aesop 

end ImpHoare

namespace ImpSwap
  open ImpSyntax ImpState ImpSemantics ImpHoare

  def SWAP : Stmt :=
    Stmt.assign "t" (fun s ↦ s "a");
    Stmt.assign "a" (fun s ↦ s "b");
    Stmt.assign "b" (fun s ↦ s "t")

  theorem SWAP_correct (a₀ b₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
      (SWAP)
    {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} := by
      apply seq_intro'
      apply seq_intro'
      apply assign_intro
      apply assign_intro
      apply assign_intro'
      aesop

end ImpSwap

namespace ImpVCG
  open Lean Lean.Parser 
  open Lean.Parser.Term Lean.Meta Lean.Elab.Tactic
  open ImpHoare ImpSyntax 

  def matchPartialHoare 
    : Expr → Option (Expr × Expr × Expr)
  | (Expr.app (Expr.app (Expr.app
       (Expr.const ``PartialHoare _) P) S) Q) =>
    Option.some (P, S, Q)
  | _ =>
    Option.none

  def applyConstant (name : Name) : TacticM Unit :=
   do
      let cst ← mkConstWithFreshMVarLevels name
      liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

  partial def vcg : TacticM Unit :=
    do
      let goals ← getUnsolvedGoals
      if goals.length != 0 then
        let target ← getMainTarget
        match matchPartialHoare target with
        | Option.none           => return
        | Option.some (P, S, _Q) =>
          if Expr.isAppOfArity S ``Stmt.skip 0 then
            if Expr.isMVar P then
              applyConstant ``skip_intro
            else
              applyConstant ``skip_intro'
          else if Expr.isAppOfArity S ``Stmt.assign 2 then
            if Expr.isMVar P then
              applyConstant ``assign_intro
            else
              applyConstant ``assign_intro'
          else if Expr.isAppOfArity S ``Stmt.seq 2 then
            andThenOnSubgoals
              (applyConstant ``seq_intro') vcg
          else if Expr.isAppOfArity S ``Stmt.ifThenElse 3 then
            andThenOnSubgoals
              (applyConstant ``if_intro) vcg
          else if Expr.isAppOfArity S ``Stmt.invWhileDo 3 then
            if Expr.isMVar P then
              andThenOnSubgoals
                (applyConstant ``invWhile_intro) vcg
            else
              andThenOnSubgoals
                (applyConstant ``invWhile_intro')
                vcg
          else
            failure

elab "vcg" : tactic =>
  vcg 

end ImpVCG

namespace SwapVCG
  open ImpVCG ImpSwap

  theorem SWAP_vcg (a₀ b₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ ∧ s "b" = b₀ *}
      (SWAP)
    {* fun s ↦ s "a" = b₀ ∧ s "b" = a₀ *} := by
    sorry 
end SwapVCG
