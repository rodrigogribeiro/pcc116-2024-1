import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic 
import Mathlib.Tactic.Linarith 

section PERM 
  variable {A : Type}

  inductive Permutation : List A → List A → Prop where
  | perm_nil : Permutation [] []
  | perm_skip : ∀ x l l', 
      Permutation l l' → Permutation (x::l) (x::l')
  | perm_swap : ∀ x y l, 
      Permutation (y::x::l) (x::y::l)
  | perm_trans : ∀ l l' l'',
      Permutation l l' →  
      Permutation l' l'' →  
      Permutation l l''

  infix:60 " ~ " => Permutation 

  -- Exercício: prove o lema de inversão para permutações 

  lemma Perm_inv (xs ys : List A) 
    : xs ~ ys → 
      (xs = [] ∧ ys = []) ∨ 
      (∃ x xs' ys', xs = x :: xs' ∧ ys = x :: ys' ∧ xs' ~ ys') ∨ 
      (∃ x y zs, xs = x :: y :: zs ∧ ys = y :: x :: zs) ∨ 
      (∃ zs, xs ~ zs ∧ zs ~ ys) := by 
      sorry 

  -- P(nil) -> (∀ x xs, P x → P (x :: xs)) -> ∀ xs, P xs

  lemma perm_refl (xs : List A) : xs ~ xs := by
    induction xs with 
    | nil =>
      constructor 
    | cons y ys IHys =>
      constructor 
      exact IHys 

  lemma perm_length_eq (xs ys : List A)(p : xs ~ ys) 
    : List.length xs = List.length ys := 
    p.rec rfl 
          (λ _x as bs _H r => by simp [r])
          (λ _x _y xs => by simp)
          (λ xs ys zs _r1 _r2 H1 H2 => by 
            simp [H1, H2])

  lemma length_eq_zero_nil (xs : List A)
    : List.length xs = 0 ↔ xs = [] := by 
    induction xs <;> simp 

  lemma perm_nil (xs : List A) :  
    [] ~ xs → xs = [] := by
    intros H 
    apply perm_length_eq at H
    rw [← length_eq_zero_nil]
    simp at * 
    simp [H]
     
  lemma perm_symm (xs ys : List A)(p : xs ~ ys) 
    : ys ~ xs :=
    p.rec Permutation.perm_nil 
          (λ x _ _ _ IH1 => 
            Permutation.perm_skip x _ _ IH1)
          (λ x y xs =>  
            Permutation.perm_swap y x xs) 
          (λ _xs _ys _zs _H1 _H2 IH1 IH2 => 
            Permutation.perm_trans _ _ _ IH2 IH1)
end PERM 

inductive Sorted : List ℕ → Prop where 
| SortedNil : Sorted []
| SortedSingle : ∀ x, Sorted (x :: [])
| SortedCons : ∀ x y ys, x ≤ y → 
              Sorted (y :: ys) → 
              Sorted (x :: y :: ys)

def insert1 (x : ℕ)(ys : List ℕ) : List ℕ := 
  match ys with 
  | [] => [x]
  | y' :: ys' => 
    match Nat.decLe x y' with 
    | isTrue _ => x :: y' :: ys' 
    | isFalse _ => y' :: insert1 x ys'

def isort (xs : List ℕ) : List ℕ := 
  match xs with 
  | [] => []
  | x :: xs => insert1 x (isort xs)

lemma insertSorted (xs : List ℕ)(x : ℕ) 
  : Sorted xs → Sorted (insert1 x xs) := by
    induction xs with 
    | nil =>
      simp [insert1]
      intros _H 
      constructor
    | cons y ys IHys =>
      intros H 
      simp [insert1] 
      rcases (Nat.decLe x y) with H1 | H1 <;> simp 
      · 
        cases H 
        case SortedSingle => 
          simp [insert1] at * 
          constructor 
          · 
            apply Nat.le_of_lt ; exact H1
          . 
            constructor 
        case SortedCons z zs H3 H2 => 
          specialize IHys H3 
          revert IHys
          simp [insert1] at * 
          rcases Nat.decLe x z with H4 | H4 <;> simp at *
          · 
            intros H5
            constructor <;> assumption
          · 
            intros H5 
            constructor <;> (try assumption)
            apply le_of_lt ; assumption 
      · 
        constructor <;> assumption

lemma insert1Perm (xs : List ℕ)(x : ℕ) 
  : (x :: xs) ~ (insert1 x xs) := by
    induction xs with 
    | nil =>
      simp [insert1]
      apply perm_refl
    | cons y ys IHys => 
      simp [insert1]
      rcases Nat.decLe x y with H1 | H1 <;> simp 
      · 
        have H2 : (x :: y :: ys) ~ (y :: x :: ys) := by 
          constructor 
        have H3 : (y :: x :: ys) ~ (y :: insert1 x ys) := by 
          constructor ; exact IHys 
        apply Permutation.perm_trans 
        exact H2 
        exact H3 
      · 
        apply perm_refl 

 
lemma isortSorted (xs : List ℕ) : Sorted (isort xs) := by
  induction xs with 
  | nil => simp [isort] ; constructor 
  | cons y ys IHys => 
    simp [isort ]
    apply insertSorted ; exact IHys 

lemma isortPerm (xs : List ℕ) : xs ~ (isort xs) := by 
  induction xs with 
  | nil => simp [isort] ; constructor 
  | cons y ys IHys => 
    simp [isort]
    have H2 : (y :: ys) ~ (y :: isort ys) := by 
      constructor ; exact IHys 
    have H3 : (y :: isort ys) ~ (insert1 y (isort ys)) := by 
      apply insert1Perm
    apply Permutation.perm_trans 
    exact H2 
    exact H3 

theorem isortCorrect (xs : List ℕ) 
  : Sorted (isort xs) ∧ xs ~ (isort xs) := by 
    apply And.intro 
    · 
      apply isortSorted 
    · 
      apply isortPerm 
