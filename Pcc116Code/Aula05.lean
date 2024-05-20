-- 2. Listas encadeadas (tipo List na biblioteca) 

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 

-- List 

inductive list (A : Type) where 
| nil : list A 
| cons : A → list A → list A 
deriving Repr
-- cons 1 (cons 2 (cons 3 nil))

open list -- 

-- length 
-- implicito {A : Type}
def size {A : Type}(xs : list A) : ℕ := 
  match xs with 
  | nil => 0 
  | cons _ xs => Nat.succ (size xs)

#eval size (cons 1 (cons 2 (cons 3 nil)))

-- repeat 
def listRepeat {A : Type}(n : ℕ)(x : A) : list A :=
  match n with 
  | Nat.zero => nil 
  | Nat.succ n' => cons x (listRepeat n' x) 

#eval listRepeat 3 false

-- append 
def cat {A : Type}(xs ys : list A) : list A := 
  match xs with 
  | nil => ys                         -- (1) 
  | cons x xs' => cons x (cat xs' ys) -- (2)

infixl:60 " .++. " => cat 

#eval (cons 1 (cons 2 nil)) .++. (cons 3 (cons 4 nil))

/-
(cons 1 (cons 2 nil)) .++. (cons 3 (cons 4 nil)) = (2)
cons 1 ((cons 2 nil) .++. (cons 3 (cons 4 nil))) = (2)
cons 1 (cons 2 (nil .++. (cons 3 (cons 4 nil)))) = (1)
cons 1 (cons 2 (cons 3 (cons 4 nil)))
-/

def reverse {A : Type}(xs : list A) : list A := 
  match xs with 
  | nil => nil   -- (1)
  | cons x' xs' => reverse xs' .++. (cons x' nil) -- (2)

/-
reverse (cons 1 (cons 2 nil)) = (2)
reverse (cons 2 nil) .++. (cons 1 nil) = (2)
(reverse nil .++. (cons 2 nil)) .++. (cons 1 nil) = (1)
(nil .++. (cons 2 nil)) .++. (cons 1 nil) = (.++. 1)
(cons 2 nil) .++. (cons 1 nil) = (.++. 2)
cons 2 (nil .++. (cons 1 nil)) = (.++. 1)
cons 2 (cons 1 nil) O(n^2)
-/


lemma cat_size {A}(xs ys : list A) : 
  size (xs .++. ys) = size xs + size ys := by  
  induction xs with 
  | nil => 
    simp [cat, size]
  | cons _x' xs' IHxs' => 
    simp [cat, size, IHxs', Nat.succ_add]

lemma listRepeat_size {A}(x : A)(n : ℕ) : 
  size (listRepeat n x) = n := by 
  induction n with 
  | zero => 
    simp [listRepeat, size]
  | succ n' IHn' => 
    simp [listRepeat, size, IHn']

lemma reverse_size {A}(xs : list A) : 
  size (reverse xs) = size xs := by 
    induction xs with 
    | nil => 
      simp [reverse] 
    | cons x' xs' IHxs' => 
      simp [reverse, cat_size, IHxs', size]

lemma cat_assoc {A}(xs ys zs : list A) 
  : xs .++. ys .++. zs = xs .++. (ys .++. zs) := by 
    induction xs with 
    | nil => 
      simp [cat]
    | cons x' xs' IHxs' => 
      simp [cat, IHxs']

lemma cat_nil_r {A}(xs : list A) 
  : xs .++. nil = xs := by 
  induction xs with 
  | nil => simp [cat]
  | cons x' xs' IHxs' =>
    simp [cat, IHxs']

lemma reverse_cat {A}(xs ys : list A) : 
  reverse (xs .++. ys) = reverse ys .++. reverse xs := by 
  induction xs with 
  | nil => 
    simp [reverse, cat, cat_nil_r]
  | cons x' xs' IHxs' => 
    simp [reverse, cat, IHxs', cat_assoc]

lemma reverse_reverse {A}(xs : list A) : 
  reverse (reverse xs) = xs := by 
  induction xs with 
  | nil => simp [reverse]
  | cons x' xs' IHxs' => 
    simp [reverse, reverse_cat, IHxs', cat]

section MAP 
  variable {A B : Type}

  -- high-order function 

  def map (f : A → B)(xs : list A) : list B := 
    match xs with 
    | nil => nil 
    | cons y ys => cons (f y) (map f ys)

  #eval map (λ x => x * 2) (cons 1 (cons 2 (cons 3 nil)))

  lemma map_id (xs : list A) 
    : map (λ x => x) xs = xs := by 
    induction xs with 
    | nil => 
      simp [map]
    | cons x' xs' IHxs' => 
      simp only [map]
      rw [IHxs']

  lemma map_app (xs ys : list A)(f : A → B)
    : map f (xs .++. ys) = (map f xs) .++. (map f ys) := by 
      induction xs with 
      | nil => simp [map, cat]
      | cons x' xs' IHxs' => 
        simp [map, cat, IHxs']

  lemma map_compose (f : A → B)(g : B → C)(xs : list A)
    : map (λ x => g (f x)) xs = (map g (map f xs)) := sorry 

end MAP 

section FILTER 
  variable {A : Type}

  def filter (p : A → Bool)(xs : list A) : list A := 
    match xs with 
    | nil => nil 
    | cons y ys => if p y then cons y (filter p ys)
                    else filter p ys

  lemma filter_cat (p : A → Bool)(xs ys : list A) : 
    filter p xs .++. filter p ys = filter p (xs .++. ys) := by 
    induction xs with 
    | nil => simp [filter, cat]
    | cons x' xs' IHxs' => 
      simp [filter, cat]
      rcases p x' with _ | _ 
      · 
        simp [IHxs']
      · 
        simp [IHxs', cat]

  
  lemma filter_reverse (p : A → Bool)(xs : list A) : 
    reverse (filter p xs) = filter p (reverse xs) := sorry 

  lemma filter_size (p : A → Bool)(xs : list A) : 
    size (filter p xs) ≤ size xs := by 
    induction xs with 
    | nil => 
      simp [size, filter]
    | cons x' xs' IHxs' => 
      simp [size, filter]
      rcases p x' with _ | _ 
      · 
        simp 
        linarith
      · 
        simp [size]
        linarith
end FILTER

section MEMBERSHIP
  variable {A : Type}

  /-
  ∀ (p : Program), Halt(p) ∨ ¬ Halt(p) : Prop 

  inductive Decidable (P : Prop) where 
  | isFalse : ¬ P → Decidable P 
  | isTrue : P → Decidable P 

  class DecidableEq (A : Type) where 
    decEq : ∀ (x y : A), Decidable (x = y)

  [DecidableEq A] -- restrição
  -/

  def member [DecidableEq A](x : A)(xs : list A) : Bool := 
    match xs with 
    | nil => false 
    | cons y ys => match decEq x y with 
                   | isFalse _ => member x ys 
                   | isTrue _ => true 

  lemma member_cat_true_left [DecidableEq A](x : A)(xs : list A) : 
    member x xs = true → member x (xs .++. ys) = true := by 
      intros H 
      induction xs with 
      | nil => simp [member] at H
      | cons x' xs' IHxs' => 
        revert H 
        simp [member] at *
        rcases decEq x x' with _ | _
        · 
          simp 
          intros H 
          apply IHxs'
          exact H 
        · 
          simp 

  lemma member_cat_true_right [DecidableEq A](x : A)(xs : list A) : 
    member x ys = true → member x (xs .++. ys) = true := sorry 

  lemma member_reverse [DecidableEq A](x : A)(xs : list A) : 
    member x xs = member x (reverse xs) := sorry 

end MEMBERSHIP
