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

lemma choice_comm 
  : ∀ e1 e2 s, s <<- (regex.choice e1 e2) → 
               s <<- (regex.choice e2 e1) := by 
    intros e1 e2 s H ; rcases H with H1 | H2 
    · 
      apply regex_match.minr 
      assumption 
    · 
      apply regex_match.minl 
      assumption 


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

def union : regex → regex → regex 
| regex.empty, e => e 
| e , regex.empty => e 
| e , e' => regex.choice e e' 

lemma union_eq : ∀ e1 e2 e3,
  e3 = union e1 e2 → 
    (e1 = e3 ∧ e2 = regex.empty) ∨ 
    (e2 = e3 ∧ e1 = regex.empty) ∨ 
    (e3 = regex.choice e1 e2) := by 
  intros e1 e2 e3 H
  rw [union] at H 
  split at H
  · 
    right 
    left 
    simp [H]
  · 
    left 
    simp [H]
  · 
    simp [H]


lemma union_sound 
  : ∀ e1 e e' s,
    e1 = union e e' → 
    s <<- e1 → 
    s <<- (regex.choice e e') := by 
    intros e1 e e' s Heq H 
    induction H with 
    | mlambda => 
      have H1 := by 
        apply union_eq 
        exact Heq 
      rcases H1 with H1 | H2 | H3
      · 
        rcases H1 with ⟨ H1, H2 ⟩ 
        simp [H1, H2] 
        apply regex_match.minl 
        constructor 
      · 
        rcases H2 with ⟨ H2 , H3 ⟩ 
        simp [H2, H3]
        apply regex_match.minr 
        constructor 
      · 
        rcases H3 
    | mchr c => 
      have H1 := by 
        apply union_eq 
        exact Heq 
      rcases H1 with H1 | H2 | H3 
      · 
        rcases H1 with ⟨ H1, H2 ⟩ 
        simp [H1, H2] 
        apply regex_match.minl 
        constructor 
      . 
        rcases H2 with ⟨ H1 , H2 ⟩ 
        simp [H1, H2]
        apply regex_match.minr 
        constructor 
      · 
        rcases H3 
    | mcat e1 e2 s1 s2 s3 H1 H2 Heq1 _IH1 _IH2 =>
      have H3 := by 
        apply union_eq 
        exact Heq 
      rcases H3 with H3 | H3 | H3 
      · 
        rcases H3 with ⟨ H1 , H2 ⟩ 
        simp [H1, H2, Heq1] 
        apply regex_match.minl 
        constructor <;> try assumption 
        rfl 
      · 
        rcases H3 with ⟨ H1 , H2 ⟩ 
        simp [H1, H2, Heq1] 
        apply regex_match.minr 
        constructor <;> try assumption 
        rfl 
      · 
        rcases H3 
    | minl e1 e2 s H1 IH1 => 
      have H2 := by 
        apply union_eq 
        exact Heq 
      rcases H2 with H2 | H2 | H2 
      · 
        rcases H2 with ⟨ H1, H2 ⟩ 
        simp [H1, H2, union] at *  
        apply regex_match.minl 
        apply regex_match.minl 
        assumption 
      · 
        rcases H2 with ⟨ H1, H2 ⟩ 
        simp [H1, H2, union] at * 
        apply regex_match.minr 
        apply regex_match.minl 
        assumption 
      · 
        rcases H2
        apply regex_match.minl 
        exact H1 
    | minr e1 e2 s H2 IH2 =>
      have H1 := by 
        apply union_eq 
        exact Heq 
      rcases H1 with ⟨ H1, H2 ⟩ | ⟨ H1, H2 ⟩ | ⟨ H1, H2 ⟩ 
      · 
        simp [H1, H2]
        apply regex_match.minl 
        apply regex_match.minr 
        assumption 
      · 
        simp [H1, H2] 
        apply regex_match.minr 
        apply regex_match.minr 
        assumption 
      · 
        apply regex_match.minr 
        exact H2 
    | mnil e =>
      have H1 := by 
        apply union_eq 
        exact Heq
      rcases H1 with ⟨ H1, H2 ⟩ | ⟨ H1, H2 ⟩ | H1 
      · 
        simp [H1, H2]
        apply regex_match.minl 
        constructor
      · 
        simp [H1, H2]
        apply regex_match.minr 
        constructor
      · 
        rcases H1 
    | mcons e1 s1 ss1 s3 H1 H2 Heq1 _IH1 _IH2 => 
      have H3 := by 
        apply union_eq 
        exact Heq 
      rcases H3 with ⟨ H1, H2 ⟩ | ⟨ H1, H2 ⟩ | H1 
      · 
        simp [H1, H2, Heq1]
        apply regex_match.minl 
        constructor <;> try assumption 
        rfl 
      · 
        simp [H1, H2, Heq1]
        apply regex_match.minr 
        constructor <;> try assumption
        rfl
      · 
        rcases H1


lemma union_complete  
  : ∀ e1 e2 e e' s,
    e2 = regex.choice e e' → 
    s <<- e2 → 
    e1 = union e e' → 
    s <<- e1 := by 
    intros e1 e2 e e' s Heq1 H Heq2
    induction H with 
    | mlambda => 
      rcases Heq1 
    | mchr c => 
      rcases Heq1 
    | mcat e1 e2 _s1 _s2 _s3 _H1 _H2 _H3 _IH1 _IH2 => 
      rcases Heq1 
    | minl e1 e2 s1 H1 IH1 => 
      rcases Heq1 
      have H2 := by 
        apply union_eq 
        exact Heq2 
      rcases H2 with ⟨ H2, H3 ⟩  | ⟨ H2, H3 ⟩  | H2 
      · 
        simp [H2, H3, union] at * 
        cases e1 <;> simp at * <;> try aesop 
        assumption
      · 
        simp [H2, H3, union] at *
        rcases H1 
      · 
        rw [H2] at *
        apply regex_match.minl
        assumption
    | minr e1 e2 s1 H2 IH2 => 
      rcases Heq1 
      have H3 := by 
        apply union_eq 
        exact Heq2 
      rcases H3 with ⟨ H2, H3 ⟩ | ⟨ H2 , H3 ⟩ | H3 
      · 
        simp [H2, H3, union] at * 
        cases e1 <;> simp at * 
        · 
          rename_i H5 
          rcases H5 
        · 
          rename_i H5 
          rcases H5 
        · 
          rename_i H5 c 
          rcases H5
        · 
          rename_i H5 e2 e3 
          rcases H5 
        · 
          rename_i H5 e1 e2 
          rcases H5 
        · 
          rename_i H5 e1 
          rcases H5 
      · 
        simp [H2, H3, union] at * 
        assumption 
      · 
        rw [H3]
        apply regex_match.minr 
        assumption 
    | mnil e1 => 
      rcases Heq1 
    | mcons e1 _s1 _s2 _s3 _H1 _H2 _H3 _IH1 _IH2 => 
      rcases Heq1 



lemma union_comm 
  : ∀ e1 e2 s, s <<- union e1 e2 → s <<- union e2 e1 := by 
    intros e1 e2 s H 
    have H1 := by 
      apply union_sound (union e1 e2) e1 e2 
      rfl 
      exact H 
    have H2 := by 
      apply choice_comm 
      exact H1 
    apply union_complete (union e2 e1) 
                         (regex.choice e2 e1)
    rfl 
    assumption 
    rfl 

def conc : regex → regex → regex 
| regex.empty , _ => regex.empty 
| regex.lambda, e => e 
| _ , regex.empty => regex.empty 
| e , regex.lambda => e 
| e , e' => regex.cat e e'

lemma conc_empty 
  : ∀ e e', regex.empty = conc e e' → 
            e = regex.empty ∨ e' = regex.empty := by 
    intros e e'
    cases e <;> cases e' <;> simp [conc] 

theorem conc_sound 
  : ∀ e1 e2 e3 s, e1 = conc e2 e3 → 
            s <<- e1 → 
            s <<- (regex.cat e2 e3) := by 
    intros e1 e2 e3 s H1 H2 
    cases e2 <;> cases e3 <;> simp [conc] at *
    all_goals (rw [H1] at H2 ; rcases H2)
    constructor <;> constructor
    constructor <;> constructor
    rename_i e1 e2 s1 s2 H2 H1 Heq
    constructor 
    constructor 
    constructor
    exact H1 
    exact Heq 
    exact H2 
    simp 
    rename_i e2 e3 H4 
    constructor 
    constructor 
    apply regex_match.minl 
    exact H4 
    simp 
    rename_i e2 e3 H3 
    constructor
    constructor 
    apply regex_match.minr 
    exact H3 
    simp 
    constructor 
    constructor 
    constructor 
    simp 
    constructor 
    constructor 
    apply regex_match.mcons 
    assumption 
    assumption 
    assumption 
    simp 
    constructor 
    constructor 
    constructor 
    simp 
    constructor
    constructor 
    constructor 
    rename_i H3 H4 
    rcases H3 
    rcases H4 
    assumption 
    constructor <;> assumption  
    constructor <;> assumption 
    constructor <;> assumption 
    constructor
    constructor <;> assumption 
    constructor 
    simp 
    constructor <;> try assumption 
    constructor <;> try assumption 
    constructor <;> try assumption 
    constructor <;> try assumption 
    constructor 
    apply regex_match.minl 
    assumption 
    constructor 
    simp 
    constructor 
    apply regex_match.minr 
    assumption 
    constructor 
    simp 
    constructor <;> try assumption 
    constructor <;> try assumption
    constructor <;> try assumption
    constructor <;> try assumption
    constructor <;> try assumption
    constructor 
    constructor 
    simp 
    constructor 
    apply regex_match.mcons <;> try assumption 
    constructor 
    simp 
    constructor 
    assumption 
    constructor 
    rename_i H3 
    rcases H3 
    assumption 
    constructor <;> try assumption 
    constructor <;> try assumption 
    constructor <;> try assumption 

theorem conc_complete 
  : ∀ e1 e2 e3 e4 s, 
    e1 = regex.cat e3 e4 → 
    s <<- e1 → 
    e2 = conc e3 e4 → 
    s <<- e2 := by 
    intros e1 e2 e3 e4 s H1 H2 H3 
    cases e1 <;> cases e2
    all_goals (rcases H1)
    have H4 := by 
      apply conc_empty
      assumption
    rcases H4 with H4 | H4 
    · 
      simp [H4, conc] at *
      rcases H2
      rename_i H5 H6 
      rcases H5 
    · 
      simp [H4] at *
      rcases H2 
      rename_i H3 
      rcases H3 
    · 
      cases e3 <;> cases e4 <;> simp [conc] at *
      rcases H2 
      rename_i H4 H5 
      rcases H4 
      rcases H5 
      simp [List.append_eq_nil] at *
      rename_i H2 
      rw [H2]
      constructor 
    · 
      cases e3 <;> cases e4 <;> simp [conc] at * 
      rcases H2
      rename_i H3 H4
      rcases H3 
      simp at *
      rename_i H5
      simp [H5, H3]
      assumption 
      rcases H2 
      rename_i H3 
      rcases H3 
      rename_i H4 
      rw [H4]
      simp [H3] 
      assumption 
    · 
      cases e3 <;> cases e4 <;> simp [conc] at * 
      rcases H2 
      rename_i H3 H4 
      rcases H3 ; aesop 
      all_goals (try aesop)
      rcases H2 
      rename_i H3 
      rcases H3 
      simp at *
      aesop 
    · 
      cases e3 <;> cases e4 <;> simp [conc] at * <;> 
      rcases H2 <;> aesop 
      rcases a_5 
      simp 
      assumption 
      rcases a_6 
      aesop 
    · 
      cases e3 <;> cases e4 <;> simp [conc] at * <;> 
      rcases H2 <;> aesop
      rcases a_3 
      simp 
      assumption 
      rcases a_4 
      aesop 

def starr : regex → regex 
| regex.empty => regex.lambda 
| regex.lambda => regex.lambda 
| regex.star e => regex.star e 
| e1 => regex.star e1

lemma star_one 
  : ∀ e s, s <<- e → s <<- (regex.star e) := by 
    intros e s H 
    have H1 : s ++ [] = s := by simp 
    rw [← H1]
    apply regex_match.mcons 
    assumption 
    apply regex_match.mnil 
    rfl 

theorem starr_sound : ∀ e1 e2 s, 
  e1 = starr e2 → 
  s <<- e1 → 
  s <<- regex.star e2 := by 
  intros e1 e2 s H1 H2 
  cases e2 <;> simp [starr] at *
  · 
    rw [H1] at H2
    rcases H2 
    constructor 
  · 
    rw [H1] at H2
    rcases H2 
    constructor 
  · 
    rw [H1] at H2 
    rcases H2 
    constructor
    rename_i H3 H4 H5 
    rw [H3]
    apply regex_match.mcons 
    exact H4 
    exact H5 
    rfl 
  · 
    rw [H1] at H2
    rcases H2 
    constructor 
    apply regex_match.mcons <;> 
    rename_i H3 H4 H5 
    exact H4 
    exact H5 
    exact H3 
  · 
    rw [H1] at H2
    rcases H2 
    constructor 
    apply regex_match.mcons <;> 
    rename_i H3 H4 H5 
    exact H4
    exact H5 
    exact H3 
  · 
    rw[H1] at H2 
    rcases H2 
    constructor 
    rename_i H3 H4 H5 
    have H6 := by 
      apply star_one 
      exact H4 
    rw [H3]
    apply regex_match.mcons 
    exact H6
    apply star_one
    exact H5 
    rfl 

lemma starr_complete 
  : ∀ e1 s, s <<- e1 → 
            s <<- (starr e1) := by 
    intros e1
    induction' e1 <;> intros s H2  
    · 
      rcases H2
    · 
      rcases H2 ; simp [starr] at *
      constructor 
    · 
      rename_i c 
      simp [starr] at *
      rcases H2 
      apply star_one 
      constructor 
    · 
      rename_i a1 a2 IH1 IH2
      rcases H2 
      rename_i H1 H2 H3 
      simp [starr]
      apply star_one 
      constructor
      exact H2 
      exact H3 
      exact H1 
    · 
      rename_i a1 a2 IH1 IH2 
      apply star_one 
      assumption 
    · 
      rename_i e1 IH1
      simp [starr] 
      assumption 

def deriv : regex → Char → regex 
| regex.empty, _ => regex.empty 
| regex.lambda, _ => regex.empty 
| regex.chr c, c' => 
  if c = c' then regex.lambda 
  else regex.empty 
| regex.choice e1 e2, c => 
  union (deriv e1 c) (deriv e2 c) 
| regex.cat e1 e2, c => 
  if nullable e1 then 
    union (deriv e2 c) (conc (deriv e1 c) e2)
  else conc (deriv e1 c) e2 
| regex.star e1,c => 
  conc (deriv e1 c) (starr e1)


theorem deriv_sound 
  : ∀ e a s, s <<- deriv e a → 
             (a :: s) <<- e := by 
    intros e 
    induction' e <;> intros a s H <;> simp [deriv] at H
    · 
      rcases H 
    · 
      rcases H 
    · 
      split at H 
      rename_i H1 
      simp [H1]
      rcases H 
      constructor 
      rcases H 
    · 
      rename_i e1 e2 IH1 IH2 
      split at H
      · 
        have H4 := by 
          apply union_sound (union (conc (deriv e1 a) e2) (deriv e2 a))
          rfl
          apply union_comm 
          exact H 
        have H5 := by 
          apply choice_comm 
          exact H4 
        rename_i Hn 
        have H3 := by 
          apply nullable_sound
          exact Hn
        rcases H5 with H5 | H5 
        · 
          rename_i H5 
          specialize IH2 a s H5 
          constructor <;> aesop 
        · 
          rename_i H5 
          have H6 := by  
            apply conc_sound (conc (deriv e1 a) e2)
            rfl 
            exact H5 
          rcases H6 
          rename_i sa sb Heq H7 H8
          simp [Heq]
          have H9 : (a :: sa) ++ sb = a :: (sa ++ sb) := by 
            rfl 
          rw [← H9]
          constructor 
          apply IH1
          exact H7 
          exact H8 
          rfl 
      · 
        have H6 := by 
          apply conc_sound (conc (deriv e1 a) e2)
          rfl 
          exact H
        rcases H6 
        rename_i s1 s2 Heq H7 H8 
        specialize IH1 a s1 H7 
        constructor
        exact IH1 
        exact H8 
        simp [Heq]
    · 
      rename_i e1 e2 IH1 IH2 
      have H1 := by 
        apply union_sound (union (deriv e1 a) (deriv e2 a))
        rfl 
        exact H 
      rcases H1 with H1 | H1 
      · 
        rename_i H2 
        specialize IH1 a s H2 
        apply regex_match.minl 
        exact IH1 
      · 
        rename_i H2 
        specialize IH2 a s H2 
        apply regex_match.minr 
        exact IH2 
    · 
      rename_i e1 IH1
      have H1 := by 
        apply conc_sound (conc (deriv e1 a) (starr e1))
        rfl 
        exact H 
      rcases H1 
      rename_i s1 s2 H2 H3 H4
      have H5 := by 
        apply starr_sound (starr e1)
        rfl 
        exact H4 
      rw [H2]
      have H6 : a :: (s1 ++ s2) = a :: s1 ++ s2 := by rfl 
      rw [H6]
      apply regex_match.mcons 
      apply IH1 
      exact H3 
      exact H5 
      rfl 

theorem deriv_complete 
  : ∀ e a s, (a :: s) <<- e → 
             s <<- (deriv e a) := by 
      intros e 
      induction' e <;> intros a s H <;> rcases H 
      · 
        simp [deriv]
        constructor 
      · 
        rename_i e1 e2 s1 s2 H1 H2 Heq IH1 IH2 
        simp [deriv]
        split 
        · 
          rename_i Hn
          sorry 
        · 
          sorry 
      all_goals sorry 
