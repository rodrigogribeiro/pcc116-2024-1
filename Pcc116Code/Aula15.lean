-- Aula 15: Modelagem de autômatos

import Mathlib.Data.Nat.Defs 
import Mathlib.Data.Fin.Basic 
import Aesop 

-- n: número de estados
-- m : número de símbolos do alfabeto 

-- definição de um DFA 

structure DFA (State Alphabet : Type) where 
  start : State  
  delta : State → Alphabet → State
  final : State → Bool

-- processamento de uma palavra δ* 

@[simp]
def deltaStarRec {S A : Type}(m1 : DFA S A) : S → List A → Bool 
| e , [] => m1.final e 
| e , c :: cs => deltaStarRec m1 (m1.delta e c) cs

def deltaStar {S A : Type}(m1 : DFA S A)(w : List A) : Bool := 
  deltaStarRec m1 m1.start w

notation:50 lhs:51 ".∈." rhs:51 => deltaStar rhs lhs
notation:50 lhs:51 ".∉." rhs:51 => ! (deltaStar rhs lhs)

-- construções sobre AFD e sua formalização

def complementDFA {S A : Type}(m1 : DFA S A) : DFA S A := 
  DFA.mk m1.start 
         m1.delta 
         (λ e => ! (m1.final e)) 

-- prova de correção 

lemma complementRec {S A : Type}(m1 : DFA S A) 
  : ∀ (w : List A)(e : S),  
    deltaStarRec m1 e w = ! deltaStarRec (complementDFA m1) e w := by 
    intros w 
    induction w with 
    | nil =>
      intros e 
      simp [complementDFA] 
    | cons c w' IH =>
      intros e 
      simp [IH]
      aesop

theorem complementCorrect {S A} 
  : ∀ (w : List A)(m1 : DFA S A), 
      (w .∈. m1) = (w .∉. (complementDFA m1)) := by 
    intros w m1 
    simp [deltaStar]
    rw [complementRec]
    aesop 

-- produto de autômatos 

def productDFA {S1 S2 A}(m1 : DFA S1 A)
                        (m2 : DFA S2 A)
                        (f : S1 × S2 → Bool) : DFA (S1 × S2) A := 
  DFA.mk (m1.start, m2.start)
         (λ p c => (m1.delta p.1 c, m2.delta p.2 c))
         f 

