import Mathlib.Tactic.Basic

-- predicate logic 

section PREDICATE_LOGIC 
  variable {U : Type}
           {u : U}
           {P Q R : U → Prop}


  lemma forall_and1 
    : (∀ x, P x ∧ Q x) → 
      ((∀ x, P x) ∧ (∀ x, Q x)) := by
    intros H 
    apply And.intro 
    · 
      intros x 
      have H1 : P x ∧ Q x := by 
        apply H 
      exact H1.left 
    · 
      intros x 
      have H2 : P x ∧ Q x := by 
        apply H 
      exact H2.right 
 
--  ** Exercício 1. 

  lemma forall_implies 
    : (∀ x, P x → Q x) → 
      (∀ y, Q y → R y) → 
      (∀ z, P z → R z) := sorry  

  lemma exists_or1 
    : (∃ x, P x ∨ Q x) →
      (∃ x, P x) ∨ (∃ y, Q y) := by 
      intros H 
      rcases H with ⟨ x, Hx ⟩ 
      rcases Hx with H1 | H2 
      · 
        left 
        exists x 
      ·   
        right 
        exists x 

end PREDICATE_LOGIC


