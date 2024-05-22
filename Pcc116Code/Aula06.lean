import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 
import Mathlib.Data.Nat.Defs 
import Mathlib.Data.List.Basic 

-- Aula 06: Predicados indutivos. 

-- * Predicado de números pares

inductive even : ℕ → Prop where 
| zero : even 0 
| succ : ∀ n, even n → even (n + 2)

example : even 8 := by 
  apply even.succ
  apply even.succ
  apply even.succ 
  apply even.succ 
  apply even.zero 


/-
even n = ∃ m, n = m * 2 -- não indutiva, recursiva

-------------------(zero)
even 0

even n 
-------------------(succ)
even (n + 2)
-/

def evenb (n : ℕ) : Bool :=
  match n with
  | 0 => true 
  | 1 => false 
  | n' + 2 => evenb n' 

-- ∀ n, P(n) ≃ P(0) ∧ (∀ n, P(n) → P(n + 1)) : Principio 
-- de indução. 
-- definição de princípios de indução.

def nat_ind  (P : ℕ → Prop)
             (base : P 0) 
             (step : ∀ n, P n → P (n + 1)) : 
             ∀ (n : ℕ), P n := λ n => 
    match n with 
    | 0 => base 
    | n' + 1 => step n' (nat_ind P base step n') -- P(n' + 1)

-- construindo provas com um princípio de indução 
-- customizado 

lemma plus_0_left (n : ℕ) : 0 + n = n := by 
  induction n using nat_ind 
  case base =>  
    simp
  case step n' _IH => 
    simp 

def nat_ind2 
  (P : ℕ → Prop)
  (zero : P 0) 
  (one : P 1) 
  (step : ∀ n, P n → P (n + 2)) : ∀ n, P n := 
  λ n =>
    match n with 
    | 0 => zero 
    | 1 => one 
    | n' + 2 => step n' (nat_ind2 P zero one step n')

lemma evenb_sound : ∀ n, evenb n = true → even n := by 
  intros n 
  induction n using nat_ind2 
  case zero => 
    intros _H 
    apply even.zero 
  case one =>
    simp [evenb]
  case step n' IH => 
    intros H 
    simp [evenb] at *
    apply even.succ 
    apply IH 
    exact H 

lemma evenb_complete : ∀ n, even n → evenb n = true := by
  intros n H 
  induction H with 
  | zero => 
    simp [evenb] 
  | succ n' H IHn' => 
    simp [evenb]
    assumption 

lemma even_twice (n : ℕ) : even (2 * n) := by 
  induction n with 
  | zero => 
    simp
    apply even.zero 
  | succ n' IHn' => 
    simp [mul_comm] 
    simp [mul_two]
    simp [Nat.succ_add, Nat.add_succ]
    apply even.succ
    simp [← mul_two, mul_comm n' 2]
    exact IHn'

lemma even_add (n m : ℕ) 
  : even n → even m → even (n + m) := sorry  

lemma even_inv (n : ℕ) : 
  even n ↔ n = 0 ∨ (∃ m, n = m + 2 ∧ even m) := sorry 

        
section EVEN_MUTUAL
  mutual
    inductive Even : ℕ → Prop where 
    | zero : Even 0 
    | succ : ∀ n, Odd n  → Even (n + 1)

    inductive Odd : ℕ → Prop where 
    | succ : ∀ n, Even n → Odd (n + 1)
  end 

  mutual 
    def even' : ℕ → Bool
    | 0 => true 
    | n + 1 => odd' n 

    def odd' : ℕ → Bool 
    | 0 => false 
    | n + 1 => even' n 
  end 


  mutual 
    lemma even'_sound (n : ℕ) 
      : even' n = true → Even n  := by
      cases n with 
      | zero => 
        intros _H 
        apply Even.zero 
      | succ n' => 
        intros H 
        simp [even'] at H
        apply Even.succ 
        apply odd'_sound ; assumption          

    lemma odd'_sound (n : ℕ)
      : odd' n = true → Odd n := by
      cases n with 
      | zero => 
        simp [odd'] at * 
      | succ n' => 
        intros H 
        simp [odd'] at H 
        apply Odd.succ 
        apply even'_sound ; assumption 
  end 
end EVEN_MUTUAL

section EVEN_PROP 
  def even_alt (n : ℕ) : Prop := ∃ m, n = 2 * m

  theorem even_even_alt (n : ℕ) 
    : even n → even_alt n := by
    intros H 
    induction H with 
    | zero => 
      exists 0
    | succ n' _Hn' IHn' =>
      rcases IHn' with ⟨ m , Heq ⟩ 
      rw [Heq]
      exists (m + 1)

  theorem even_alt_even (n : ℕ)
    : even_alt n → even n := by
    intros H 
    rcases H with ⟨ m , Heq ⟩ 
    rw [Heq] 
    apply even_twice 
end EVEN_PROP 

-- * predicado de pertencer a uma lista 

section IN 
  variable {A : Type}
/-
-------------- (Here)
x ∈ (x :: xs)

x ∈ ys 
---------------(There)
x ∈ (y :: ys)
-/


  inductive In (x : A) : List A → Prop where
  | Here : ∀ xs, In x (x :: xs)
  | There : ∀ y ys, In x ys → In x (y :: ys)

  def member (x : ℕ)(xs : List ℕ) : Bool := 
    match xs with 
    | [] => false 
    | (y :: ys) => 
      match Nat.decEq x y with 
      | isFalse _ => member x ys 
      | isTrue _ => true 

  lemma member_sound (x : ℕ)(xs : List ℕ) 
    : member x xs = true → In x xs := by 
    induction xs with
    | nil => 
      simp [member]
    | cons y ys IHys => 
      simp [member] 
      rcases Nat.decEq x y with H1 | H1 
      · 
        simp 
        intros H 
        apply In.There 
        apply IHys 
        exact H 
      · 
        simp
        rw [H1]
        apply In.Here 

  lemma member_complete (x : ℕ) xs 
    : In x xs → member x xs = true := by 
    intros H 
    induction H 
    case Here => 
      simp [member]
      rcases Nat.decEq x x with H1 | _H1 
      · 
        contradiction  
      · 
        simp 
    case There y ys Hys IH => 
      simp [member]
      generalize H2 : Nat.decEq x y = p
      rcases p with H1 | H1 
      · 
        simp 
        exact IH 
      · 
        simp

  lemma In_app_right (x : ℕ) xs ys 
    : In x xs → In x (xs ++ ys) := 
    sorry 

  lemma In_app_left (y : ℕ) ys xs 
    : In y ys → In y (xs ++ ys) := 
    sorry 

  lemma In_app_inv (x : ℕ) xs ys 
    : In x (xs ++ ys) → In x xs ∨ In x ys := 
    sorry 
end IN


