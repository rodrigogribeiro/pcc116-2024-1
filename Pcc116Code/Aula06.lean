import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 
import Mathlib.Data.Nat.Defs 

-- Aula 06: Predicados indutivos. 

-- * Predicado de números pares

inductive even : ℕ → Prop where 
| zero : even 0 
| succ : ∀ n, even n → even (n + 2)

def evenb (n : ℕ) : Bool :=
  match n with
  | 0 => true 
  | 1 => false 
  | n' + 2 => evenb n' 

theorem evenb_sound (n : ℕ) 
  : evenb n = true → even n  := by 
    sorry 


/-
even n = ∃ m, n = m * 2 -- não indutiva, recursiva

-------------------(zero)
even 0

even n 
-------------------(succ)
even (n + 2)
-/

example : even 8 := by 
  apply even.succ
  apply even.succ
  apply even.succ 
  apply even.succ 
  apply even.zero 

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

lemma even_add (n m : ℕ) : even n → even m → even (n + m) := sorry  

lemma even_inv (n : ℕ) : 
  even n ↔ n = 0 ∨ (∃ m, n = m + 2 ∧ even m) := sorry 


-- * predicado de pertencer a uma lista 

section IN 
  variable {A : Type}

  inductive In (x : A) : List A → Prop where
  | Here : ∀ xs, In x (x :: xs)
  | There : ∀ y ys, In x ys → In x (y :: ys)

  def member [DecidableEq A](x : A)(xs : List A) : Bool := sorry 

  lemma member_sound [DecidableEq A](x : A)(xs : List A) 
    : member x xs = true → In x xs := 
    sorry 

  lemma member_complete [DecidableEq A](x : A) xs 
    : In x xs → member x xs = true := 
    sorry 

  lemma In_app_right [DecidableEq A] (x : A) xs ys 
    : In x xs → In x (xs ++ ys) := 
    sorry 

  lemma In_app_left [DecidableEq A] (y : A) ys xs 
    : In y ys → In y (xs ++ ys) := 
    sorry 

  lemma In_app_inv [DecidableEq A](x : A) xs ys 
    : In x (xs ++ ys) → In x xs ∨ In x ys := 
    sorry 
end IN


