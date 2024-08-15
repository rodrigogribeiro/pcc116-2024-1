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

-- repeat 
def listRepeat {A : Type}(n : ℕ)(x : A) : list A :=
  match n with 
  | Nat.zero => nil 
  | Nat.succ n' => cons x (listRepeat n' x) 

-- append 
def cat {A : Type}(xs ys : list A) : list A := 
  match xs with 
  | nil => ys                         -- (1) 
  | cons x xs' => cons x (cat xs' ys) -- (2)

infixl:60 " .++. " => cat 

def reverse {A : Type}(xs : list A) : list A := 
  match xs with 
  | nil => nil   -- (1)
  | cons x' xs' => reverse xs' .++. (cons x' nil) -- (2)

def rev {A : Type}(xs ac : list A) : list A := 
  match xs with 
  | nil => ac 
  | cons x' xs' => rev xs' (cons x' ac)

#check Nat.succ_add 

lemma cat_size {A}(xs ys : list A) : 
  size (xs .++. ys) = size xs + size ys := by  
  induction xs with 
  | nil =>
    simp [size, cat]
  | cons x' xs' IH => 
    simp [size, cat, IH, Nat.succ_add]

lemma listRepeat_size {A}(x : A)(n : ℕ) : 
  size (listRepeat n x) = n := by 
  sorry 

lemma reverse_size {A}(xs : list A) : 
  size (reverse xs) = size xs := by 
  sorry 

lemma cat_assoc {A}(xs ys zs : list A) 
  : xs .++. ys .++. zs = xs .++. (ys .++. zs) := by 
  sorry 

lemma cat_nil_r {A}(xs : list A) 
  : xs .++. nil = xs := by 
  sorry 

lemma reverse_cat {A}(xs ys : list A) : 
  reverse (xs .++. ys) = reverse ys .++. reverse xs := by 
  sorry 

lemma reverse_reverse {A}(xs : list A) : 
  reverse (reverse xs) = xs := by 
  sorry 

lemma reverse_rev {A}(xs : list A) : 
  reverse xs = rev xs nil := by 
  sorry 
  

section MAP 
  variable {A B : Type}

  -- high-order function 

  def map (f : A → B)(xs : list A) : list B := 
    match xs with 
    | nil => nil 
    | cons y ys => cons (f y) (map f ys)


  lemma map_id (xs : list A) 
    : map (λ x => x) xs = xs := by 
    sorry 

  lemma map_app (xs ys : list A)(f : A → B)
    : map f (xs .++. ys) = (map f xs) .++. (map f ys) := by 
    sorry 

  lemma map_compose (f : A → B)(g : B → C)(xs : list A)
    : map (λ x => g (f x)) xs = (map g (map f xs)) := sorry 

end MAP 

section FILTER 
  variable {A : Type}

  def filter (p : A → Bool)
             (xs : list A) : list A := 
    match xs with 
    | nil => nil 
    | cons y ys => 
      if p y then cons y (filter p ys)
      else filter p ys

  lemma filter_cat (p : A → Bool)
                   (xs ys : list A) : 
    filter p xs .++. filter p ys = 
    filter p (xs .++. ys) := by 
    induction xs with
    | nil => 
      simp [filter, cat]
    | cons x' xs' IH => 
      simp [filter, cat]
      split
      ·
        simp [cat, IH]
      · 
        simp [IH]

  lemma filter_reverse (p : A → Bool)
                       (xs : list A) : 
    reverse (filter p xs) = 
    filter p (reverse xs) := by 
    sorry 

  lemma filter_size (p : A → Bool)(xs : list A) : 
    size (filter p xs) ≤ size xs := by
    sorry 

  lemma filter_and (p q : A → Bool)
                   (xs : list A) : 
    filter p (filter q xs) = 
    filter (λ x => p x && q x) xs := by 
    induction xs with 
    | nil => 
      simp [filter]
    | cons x' xs' IH =>
      simp [filter]
      have H1 : ∃ b, p x' = b := by 
        exists (p x') 
      have H2 : ∃ b, q x' = b := by 
        exists (q x') 
      rcases H1 with ⟨ _ | _ , H1 ⟩ 
      · 
        rcases H2 with ⟨ _ | _, H2 ⟩ 
        · 
          simp [filter, H1, H2, IH]
        · 
          simp [filter, H1, H2, IH]
      · 
        rcases H2 with ⟨ _ | _, H2 ⟩ 
        · 
          simp [filter, H1, H2, IH]
        · 
          simp [filter, H1, H2, IH]
end FILTER


section MEMBERSHIP
  variable {A : Type}

  def member [DecidableEq A](x : A)
                            (xs : list A) : Bool := 
    match xs with 
    | nil => false 
    | cons y ys => match decEq x y with 
                   | isFalse _ => member x ys 
                   | isTrue _ => true 

  lemma member_cat_true_left [DecidableEq A]
                             (x : A)
                             (xs : list A) : 
    member x xs = true → 
    member x (xs .++. ys) = true := by
    induction xs with 
    | nil => 
      simp [member]
    | cons x' xs' IH => 
      simp [member]
      split 
      · 
        exact IH 
      · 
        simp 

  lemma member_cat_true_right [DecidableEq A](x : A)(xs : list A) : 
    member x ys = true → member x (xs .++. ys) = true := sorry 

  lemma member_reverse [DecidableEq A](x : A)(xs : list A) : 
    member x xs = member x (reverse xs) := sorry 

end MEMBERSHIP
