-- Aula 04. Programação funcional e recursividade 

import Mathlib.Tactic.Basic

-- 1. Números Naturais (definidos na biblioteca: Tipo Nat)

inductive N where 
| zero : N 
| succ : N → N 
deriving Repr 
-- zero, succ zero, succ (succ zero), ...

-- convertendo entre N e Nat 

def toN (n : Nat) : N := 
  match n with 
  | 0 => N.zero 
  | k + 1 => N.succ (toN k)

#eval toN 5

-- definindo a adição 

def plus (n m : N) : N := 
  match n with 
  | N.zero => m                       -- 1
  | N.succ n' => N.succ (plus n' m)   -- 2 

open N 

infixl:60 " .+. " => plus 

-- Lousa: execução de plus (succ (succ zero)) (succ zero) 
-- representando N como números 
/-
(succ (succ zero)) .+. (succ zero) = por 2 
succ ((succ zero) .+. (succ zero)) = por 2 
succ (succ (zero .+. (succ zero))) = por 1 
succ (succ (succ zero))
-/
-- Primeiro lemma simples 

-- obter uma igualdade trivial (x = x) por simplificação 
-- dizemos que essa igualdade vale por *definição*

lemma plus_0_l (n : N) : zero .+. n = n := by 
  simp only [plus]

-- Segundo lemma 

lemma plus_0_r (n : N) : n .+. zero = n := by
  induction n with 
  | zero => 
    simp only [plus]
  | succ n' IHn' => 
    simp only [plus, IHn']
    

lemma plus_succ m n : succ (m .+. n) = m .+. succ n := by 
  induction m with 
  | zero => 
    simp only [plus]
  | succ m' IHm' => 
    simp only [plus, IHm']

theorem plus_comm (n m : N) : n .+. m = m .+. n := by 
  induction n with 
  | zero => 
    simp only [plus, plus_0_r]
  | succ n' IHn' => 
    simp only [plus, IHn', plus_succ]




theorem plus_assoc (n m p) 
  : n .+. m .+. p = n .+. (m .+. p) := sorry 

-- definição de double 

def double (n : N) : N := 
  match n with 
  | zero => zero 
  | succ n' => succ (succ (double n'))

lemma double_correct n : double n = n .+. n := sorry 

-- teste de igualdade 

def eqN (n m : N) : Bool := 
  match n , m with 
  | zero, zero => true 
  | succ n', succ m' => eqN n' m' 
  | _ , _ => false 

lemma eqN_refl n : eqN n n = true := sorry 

lemma eqN_correct : eqN n m = true → n = m := sorry 

-- definição da multiplicação e prova de comutatividade 
-- e associatividade.


-- Números em binário
/-
Considere o tipo de dados seguinte que representa 
números em binário de forma que o bit mais significativo 
esteja mais a direita e não à esquerda, como usual. 
-/

inductive B where
| Z : B 
| B0 : B → B 
| B1 : B → B 
deriving Repr 

/-
A seguir, mostramos alguns exemplos de números naturais
e sua representação usando o tipo B 

Número natural  Valor do tipo B 
0               Z 
1               B1 Z 
2               B0 (B1 Z)
3               B1 (B0 (B1 Z))
4               B0 (B0 (B1 Z))
...
-/

/-
Desenvolva a função incr que incrementa de um 
um valor de tipo B. 
-/

def incr (b : B) : B := sorry 

/-
Desenvolva a função B2N que converte um valor de 
tipo B em um equivalente de tipo N.
-/

def B2N (b : B) : N := sorry 

/-
Desenvolva a função N2B que converte um valor de 
tipo N em um equivalente de tipo B. Dica: use a 
função incr. 
-/

def N2B (n : N) : B := sorry 

/-
Prove que a operação incr preserva a função 
B2N.
-/

lemma incr_preserves_b2n b : 
  B2N (incr b) = succ (B2N b) := sorry 

/-
Utilizando o lema anterior, prove que as funções 
B2N e N2B são inversas.
-/

theorem N2B2N n : B2N (N2B n) = n := sorry 
