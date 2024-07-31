import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 
import Mathlib.Data.Nat.Defs 
import Mathlib.Data.List.Basic 

set_option autoImplicit false

-- Aula 06: Predicados indutivos. 

-- * Predicado de números pares

inductive even : ℕ → Prop where 
| zero : even 0 
| succ : ∀ n, even n → even (n + 2)

example : even 8 := by 
  sorry 
/-
evenn = ∃ m, n = m * 2 -- não indutiva, recursiva

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
  sorry 

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
  sorry 

lemma evenb_complete : ∀ n, even n → evenb n = true := by
  intros n H 
  induction H with 
  | zero => 
    simp [evenb] 
  | succ n' H IHn' => 
    simp [evenb]
    assumption 

lemma even_twice (n : ℕ) : even (2 * n) := by 
  sorry 
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
    sorry 

  lemma member_complete (x : ℕ) xs 
    : In x xs → member x xs = true := by
    sorry 

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

section RE 

  inductive regex where 
  | empty : regex  
  | lambda : regex  
  | chr : Char → regex  
  | cat : regex → regex → regex 
  | choice : regex → regex → regex 
  | star : regex → regex 
  deriving Repr 

  inductive regex_match : List Char → regex → Prop where 
  | mlambda : regex_match [] regex.lambda  
  | mchr : ∀ c, regex_match [c] (regex.chr c)
  | mcat : ∀ e1 e2 s1 s2, regex_match s1 e1 → 
                          regex_match s2 e2 → 
                          regex_match (s1 ++ s2) 
                                      (regex.cat e1 e2)
  | minl : ∀ e1 e2 s1, regex_match s1 e1 → 
                       regex_match s1 (regex.choice e1 e2)
  | minr : ∀ e1 e2 s2, regex_match s2 e2 → 
                       regex_match s2 (regex.choice e1 e2)
  | mnil : ∀ e1, regex_match [] (regex.star e1)
  | mcons : ∀ e1 s1 ss1, regex_match s1 e1 → 
                         regex_match ss1 (regex.star e1) → 
                         regex_match (s1 ++ ss1) 
                                     (regex.star e1)

  infix:60 " <<- " => regex_match 

  lemma mcons1 : ∀ e1 s1, s1 <<- e1 → 
                          s1 <<- (regex.star e1) := by 
    sorry   
  
  lemma empty_is_empty : ∀ s, ¬ (s <<- regex.empty ) := by 
    sorry 

  lemma m_union : ∀ e1 e2 s, 
      s <<- e1 ∨ s <<- e2 → s <<- (regex.choice e1 e2) := by 
      sorry 

  lemma m_star 
    : ∀ (ss : List (List Char))(e : regex), 
      (∀ s, s ∈ ss → s <<- e) → 
      List.foldr List.append [] ss <<- (regex.star e) := by 
    sorry 
  
  def regex_chars (e : regex) : List Char := sorry 

  lemma star_append' : ∀ s1 e e',
    e' = regex.star e →  
    s1 <<- e' → 
    ∀ s2, s2 <<- (regex.star e) → 
    (s1 ++ s2) <<- (regex.star e) := by 
    intros s1 e e' Heq H 
    induction H with 
    | mlambda => 
      intros s2 Hs2
      simp 
      assumption 
    | mchr c => 
      intros s2 _Hs2 
      simp at Heq 
    | mcat e1 e2 s2 s3 _H1 _H2 _IH1 _IH2 => 
      intros s2 _Hs2 
      simp at Heq
    | minl e1 e2 s1 _H1 _IH1 => 
      intros s2 _Hs2 
      simp at Heq 
    | minr e1 e2 s1 _H1 _IH1 => 
      intros s2 _Hs2 
      simp at Heq 
    | mnil e1 => 
      intros s2 Hs2 
      simp 
      assumption 
    | mcons e1 s2 ss1 H1 H11 IH1 IH11 => 
      intros s3 Hs2 
      rcases Heq 
      rw [List.append_assoc]
      constructor 
      · 
        assumption 
      · 
        apply IH11 
        simp 
        assumption 

  theorem star_append : ∀ s1 e,  
    s1 <<- (regex.star e) → 
    ∀ s2, s2 <<- (regex.star e) → 
    (s1 ++ s2) <<- (regex.star e) := by 
    intros s1 e Hs1 s2 Hs2 
    apply star_append' <;> try assumption 
    rfl 

  -- lema do bombeamento 

  def pumping_value : regex → ℕ 
  | regex.empty => 1
  | regex.lambda => 1 
  | regex.chr _ => 2 
  | regex.cat e1 e2 => 
    pumping_value e1 + pumping_value e2 
  | regex.choice e1 e2 => 
    pumping_value e1 + pumping_value e2 
  | regex.star e1 => 
    pumping_value e1 

  lemma pumping_value_ge_1 : ∀ e, pumping_value e ≥ 1 := by 
    intros e 
    induction e with 
    | empty => 
      simp [pumping_value]
    | lambda => 
      simp [pumping_value]
    | chr _ => 
      simp [pumping_value]
    | cat e1 e2 IHe1 IHe2 => 
      simp [pumping_value]
      linarith 
    | choice e1 e2 IHe1 IHe2 => 
      simp [pumping_value]
      linarith 
    | star e1 IHe1 => 
      simp [pumping_value]
      linarith 

  lemma pumping_value_neq_0 : ∀ e, pumping_value e ≠ 0 := by 
    intros e 
    induction e with 
    | empty => 
      simp [pumping_value]
    | lambda => 
      simp [pumping_value]
    | chr _ => 
      simp [pumping_value]
    | cat e1 e2 IH1 IH2 => 
      simp [pumping_value, IH1, IH2]
    | choice e1 e2 IH1 IH2 => 
      simp [pumping_value, IH1, IH2]
    | star e1 IH1 => 
      simp [pumping_value, IH1]
   
  def napp (n : ℕ)(s : List Char) : List Char := 
    match n with 
    | 0 => []
    | n' + 1 => s ++ napp n' s

  lemma napp_nil : ∀ n, napp n [] = [] := by 
    intros n 
    induction n with 
    | zero => 
      simp [napp]
    | succ n' IH => 
      simp [napp, IH]

  lemma napp_append 
    : ∀ n m s, napp (n + m) s = napp n s ++ napp m s := by 
    sorry 

  lemma napp_star 
    : ∀ n s1 s2 e, 
      s1 <<- e → 
      s2 <<- (regex.star e) → 
      (napp n s1 ++ s2) <<- (regex.star e) := by 
    sorry 

  lemma sum_le_or : ∀ (a b c d : ℕ),
    a + b ≤ c + d → (a ≤ c) ∨ (b ≤ d) := by 
    intros a b c d H 
    omega 

  theorem pumping_lemma 
    : ∀ e z, z <<- e → 
             pumping_value e ≤ List.length z →
      ∃ u v w, z = u ++ v ++ w ∧  
               List.length (u ++ v) ≤ pumping_value e ∧  
               ∀ i, (u ++ napp i v ++ w) <<- e := by 
      intros e z H 
      induction H with 
      | mlambda => 
        intros H1 
        exists []
      | mchr c =>
        intros H1 
        exists []
      | mcat e1 e2 s1 s2 H1 H2 IH1 IH2 => 
        intros H3
        simp [pumping_value] at H3
        have H31 : pumping_value e1 ≤ List.length s1 ∨ 
                   pumping_value e2 ≤ List.length s2 := by 
          apply sum_le_or ; assumption 
        rcases H31 with H31 | H31 
        · 
          have H4 : ∃ u v w, s1 = u ++ v ++ w ∧ 
                            List.length (u ++ v) ≤ pumping_value e1 ∧ 
                            ∀ (i : ℕ), u ++ napp i v ++ w <<- e1 := by 
            apply IH1 ; assumption 
          rcases H4 with ⟨ u1, v1, w1, Heqs1, H3le, H3i ⟩
          exists u1 
          exists v1
          exists (w1 ++ s2)
          rw [← List.append_assoc, Heqs1]
          simp 
          apply And.intro 
          · 
            simp [pumping_value]
            rw [Heqs1] at H3
            simp [List.length_append] at H3le
            omega
          · 
            intros i 
            have H5 : u1 ++ (napp i v1 ++ (w1 ++ s2)) = 
                      (u1 ++ napp i v1 ++ w1) ++ s2 := by 
              simp [List.append_assoc]
            rw [H5]
            constructor 
            apply H3i
            assumption
        · 
          sorry 
      | minl e1 e2 s1 H1 IH1 => 
        intros H2 
        simp [pumping_value] at H2 
        have H3 : pumping_value e1 ≤ List.length s1 := by 
          omega 
        have H4 : ∃ u v w, s1 = u ++ v ++ w ∧ 
                  List.length (u ++ v) ≤ pumping_value e1 ∧ 
                  ∀ (i : ℕ), u ++ napp i v ++ w <<- e1 := by 
          apply IH1 ; assumption 
        rcases H4 with ⟨ u1, v1, w1, Heqs1, Hles1, His1 ⟩ 
        exists u1
        exists v1 
        exists w1 
        simp [Heqs1, pumping_value]
        rw [Heqs1] at H2
        simp [List.length_append] at Hles1 
        apply And.intro 
        · 
          omega 
        · 
          intros i 
          rw [← List.append_assoc]
          constructor 
          apply His1
      | minr e1 e2 H2 IH2 => sorry 
      | mnil e1 => 
        intros H 
        simp [pumping_value] at *
        rw [H]
        simp 
        exists []
        exists []
        exists []
        simp [napp_nil]
        constructor 
      | mcons e1 s1 s2 H1 H2 IH1 IH2 => sorry 

end RE 
