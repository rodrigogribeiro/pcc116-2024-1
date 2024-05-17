-- 2. Listas encadeadas (tipo List na biblioteca) 

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 

-- List 

inductive list (A : Type) where 
| nil : list A 
| cons : A → list A → list A 

-- cons 1 (cons 2 (cons 3 nil))

open list -- 

-- length 
-- implicito {A : Type}
def size {A : Type}(xs : list A) : ℕ := 
  match xs with 
  | nil => 0 
  | cons _ xs => Nat.succ (size xs)

def listRepeat {A : Type}(n : Nat)(x : A) : list A :=
  match n with 
  | Nat.zero => nil 
  | Nat.succ n' => cons x (listRepeat n' x) 

def cat {A : Type}(xs ys : list A) : list A := 
  match xs with 
  | nil => ys 
  | cons x xs' => cons x (cat xs' ys)

infixl:60 " .++. " => cat 

def reverse {A : Type}(xs : list A) : list A := 
  match xs with 
  | nil => nil
  | cons x' xs' => reverse xs' .++. (cons x' nil)


lemma cat_size {A}(xs ys : list A) : 
  size (xs .++. ys) = size xs + size ys := by 
  induction xs with 
  | nil => 
    simp [size, cat] 
  | cons x' xs' IHxs' => 
    simp [size, cat]
    rw [IHxs']
    simp [Nat.succ_add]

lemma listRepeat_size {A}(x : A)(n : Nat) : 
  size (listRepeat n x) = n := sorry 

lemma reverse_size {A}(xs : list A) : 
  size (reverse xs) = size xs := sorry 

lemma reverse_cat {A}(xs ys : list A) : 
  reverse (xs .++. ys) = reverse ys .++. reverse xs := sorry 

lemma reverse_reverse {A}(xs : list A) : 
  reverse (reverse xs) = xs := sorry 

section MAP 
  variable {A B : Type}

  def map (f : A → B)(xs : list A) : list B := 
    match xs with 
    | nil => nil 
    | cons y ys => cons (f y) (map f ys)

  lemma map_id (xs : list A) 
    : map (λ x => x) xs = xs := sorry 

  lemma map_app (xs ys : list A)(f : A → B)
    : map f (xs .++. ys) = (map f xs) .++. (map f ys) := sorry  

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

  lemma filter_size (p : A → Bool)(xs : list A) : 
    size (filter p xs) ≤ size xs := sorry  

end FILTER 
