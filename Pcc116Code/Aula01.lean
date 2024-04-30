import Mathlib.Tactic.Basic

section PropLogic 

  variable (A B C : Prop)

  theorem first_theorem : (A → B) → A → B := by
    /-
     G U {H : A} |- B
     --------------      intros H
     G |- A -> B


     H : A <- G
     -----------         exact H
     G |- A
    -/
    intros H -- introdução da implicação  
    exact H

  #print first_theorem

  theorem first2 : (A → B) → A → B := 
    λ H : A → B => H


-- *** Exercício 1.

  lemma ex1 : A → B → A := by sorry 


-- *** Exercício 2.

  lemma ex2 : (A → B) → (B → C) → A → C := by  
    intros H1 H2 H3
    /-
      G |- B -> C     G |- B 
      ----------------------- apply 
          G |- C
    -/
    apply H2
    apply H1
    exact H3
    

-- ** Conjunção 
-- par 

  theorem and_comm1 : (A ∧ B) → (B ∧ A) := by 
    intros H1
    apply And.intro
    ·
      exact H1.right
    · 
      rcases H1 with ⟨ H1 , _H2 ⟩
      exact H1


  theorem and_assoc1 : A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
    intros H
    rcases H with ⟨ HA , HB , HC ⟩
    apply And.intro 
    · 
      apply And.intro <;> assumption
    · 
      assumption 


-- *** Exercício 3

  theorem ex3 : (A ∧ B) ∧ C -> A ∧ (B ∧ C) := sorry 

-- *** Exercício 4

  theorem ex4 : ((A ∧ B) → C) → (A → B → C) := sorry 

-- *** Exercício 5

  theorem ex5 : (A → B → C) → ((A ∧ B) → C) := sorry 

-- *** Exercício 6

  theorem ex6 : ((A → B) ∧ (A → C)) → A → (B ∧ C) := sorry 

  -- A ↔ B = (A → B) ∧ (B → A)

  lemma iff_demo : (A ∧ B) ↔ (B ∧ A) := by 
    apply Iff.intro           <;> 
    intros H                  <;> 
    rcases H with ⟨ H1 , H2 ⟩ <;> 
    apply And.intro           <;> 
    assumption  

  
-- Negação  

  lemma modus1 : ((A → B) ∧ ¬ B) → ¬ A := sorry 

  lemma contraEx : A → ¬ A → B := sorry 

-- disjunção 

  lemma or_comm1 : (A ∨ B) ↔ (B ∨ A) := sorry 
  lemma orex2 : ((A ∨ B) ∧ ¬ A) → B := sorry 

-- Exercício 8

  lemma ex8 : (A ∨ (B ∧ C)) -> (A ∨ B) ∧ (A ∨ C) := sorry 

-- Lógica clássica

  open Classical 

  #check (em A)

  lemma doubleNeg : ¬ (¬ A) ↔ A := sorry 

-- Exercício 9

  lemma ex9 : (¬ B → ¬ A) → (A → B) := sorry 

-- Exercício 10

  lemma ex10 : ((A → B) → A) → A := sorry 

end PropLogic
