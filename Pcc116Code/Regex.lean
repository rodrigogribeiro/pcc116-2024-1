import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Defs 
import Aesop 

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
| mcat : ∀ e1 e2 s1 s2 s3, 
  regex_match s1 e1 → 
  regex_match s2 e2 → 
  s3 = s1 ++ s2 → 
  regex_match s3 (regex.cat e1 e2)
| minl : ∀ e1 e2 s1, 
  regex_match s1 e1 → 
  regex_match s1 (regex.choice e1 e2)
| minr : ∀ e1 e2 s2, 
  regex_match s2 e2 → 
  regex_match s2 (regex.choice e1 e2)
| mnil : ∀ e1,
  regex_match [] (regex.star e1)
| mcons : ∀ e1 s1 ss1 s3, 
  regex_match s1 e1 → 
  regex_match ss1 (regex.star e1) → 
  s3 = s1 ++ ss1 → 
  regex_match s3 (regex.star e1)

infix:60 " <<- " => regex_match 

def nullable : regex → Bool 
| regex.empty => false 
| regex.lambda => true 
| regex.chr _ => false 
| regex.cat e1 e2 => nullable e1 && nullable e2 
| regex.choice e1 e2 => 
  nullable e1 || nullable e2 
| regex.star _ => true 

theorem nullable_sound 
  : ∀ e, nullable e = true → [] <<- e := by 
    intros e 
    induction e with 
    | empty => 
      intros H 
      simp [nullable] at H  
    | lambda => 
      intros _H
      constructor 
    | chr c =>
      intros H 
      simp [nullable] at H 
    | cat e1 e2 IHe1 IHe2 =>
      intros H 
      simp [nullable] at H 
      have Heq : @List.nil Char = [] ++ [] := by
        simp
      rw [Heq]
      rcases H with ⟨ H1 , H2 ⟩ 
      constructor
      · 
        apply IHe1 ; assumption 
      · 
        apply IHe2 ; assumption
      · 
        simp 
    | choice e1 e2 IHe1 IHe2 => 
      intros H 
      simp [nullable] at H
      rcases H with H1 | H2 
      · 
        apply regex_match.minl 
        apply IHe1 ; assumption 
      · 
        apply regex_match.minr 
        apply IHe2 ; assumption
    | star e1 _IHe1 => 
      intros _H
      constructor

theorem nullable_complete 
  : ∀ e, [] <<- e → nullable e = true := by 
    intros e 
    induction e with 
    | empty => 
      intros H
      cases H
    | lambda =>
      intros _H 
      simp [nullable]
    | chr c => 
      intros H 
      cases H 
    | cat e1 e2 IHe1 IHe2 => 
      intros H 
      simp [nullable] 
      rcases H 
      rename_i H2 H1 Heq
      simp [List.append_eq_nil] at H2
      rcases H2 with ⟨ H2, H3 ⟩ 
      constructor 
      · 
        apply IHe1 
        simp [H2] at *
        assumption
      · 
        apply IHe2 
        simp [H3] at * 
        assumption 
    | choice e1 e2 IHe1 IHe2 =>
      intros H 
      simp [nullable]
      rcases H 
      · 
        rename_i H1 
        left 
        apply IHe1 
        assumption 
      · 
        rename_i H1 
        right 
        apply IHe2 
        assumption 
    | star e1 _IHe1 => 
      intros _H 
      simp [nullable]
