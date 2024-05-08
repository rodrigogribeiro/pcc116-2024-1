import Mathlib.Tactic.Basic

-- predicate logic 

section PREDICATE_LOGIC 
  variable {U : Type}
           {u : U}
           {P Q R : U → Prop}


  lemma forall_and1 
    : (∀ x, P x ∧ Q x) → ((∀ x, P x) ∧ (∀ x, Q x)) := by 
      intros H 
      apply And.intro 
      · 
        intros a 
        have H2 : P a ∧ Q a := by 
          apply H 
        exact H2.left 
      · 
        intros x 
        have H2 : P x ∧ Q x := by 
          apply H 
        exact H2.right

  lemma forall_implies 
    : (∀ x, P x → Q x) → 
      (∀ y, Q y → R y) → 
      (∀ z, P z → R z) := sorry  

  lemma exists_or1 
    : (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ y, Q y) := by 
      intros H 
      rcases H with ⟨ x , H1 ⟩ 
      rcases H1 with H3 | H4 
      · 
        left 
        exists x 
      · 
        right 
        exists x
  
end PREDICATE_LOGIC


