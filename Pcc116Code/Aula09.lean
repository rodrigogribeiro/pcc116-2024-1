-- Aula 09: Recursão geral 

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 
import Mathlib.Data.Nat.Defs

-- definições parciais: uma maneira de contornar a 
-- exigência de totalidade

partial def pdiv (n m : ℕ) : ℕ × ℕ := 
  match Nat.decLt n m with 
  | isTrue _ => (0, m)
  | _           => 
    match pdiv (n - m) m with
    | (q,r) => (q + 1, r)

-- Lean não identifica a chamada a pdif (n - m) m 
-- como seguindo uma cadeia decrescente finita de 
-- chamadas. Como resolver esse dilema?

-- Estratégia 1. uso de fuel 

def fuel_div_def (fuel : ℕ)(n m : ℕ) : Option (ℕ × ℕ) := 
  match fuel with 
  | 0 => .none 
  | fuel' + 1 => 
    match Nat.decLt n m with 
    | isTrue _ => .some (0,m)
    | _ => match fuel_div_def fuel' n m with 
           | .none => .none 
           | .some (q,r) => .some (q + 1, r)

def fuel_div (n m : ℕ) : Option (ℕ × ℕ) := 
  fuel_div_def n n m

-- Problemas:
-- 1. Necessidade de usar o tipo Option para garantir totalidade
--    quando não há combustível suficiente para executar 
--    chamadas recursivas.
-- 2. Presença de um parâmetro artificial, o fuel. 

-- Estratégia 2. uso de relações de ordem bem formadas 

-- Relações bem formadas 

/-
Primeiro, temos que lembrar o que é uma relação de ordem.

Dizemos que R é uma relação de ordem se:

- R é irreflexiva: ∀ x, ¬ R x x 
- R é transitiva: ∀ x y z, R x y → R y z → R x z

Dizemos que uma relação de ordem é bem formada se 
todos os elementos desta relação são _alcançáveis_.

Para entender o conceito de alcançabilidade, é 
útil recordar sobre o princípio de indução forte. 
-/

def strong_induction (P : ℕ → Prop) 
  : (∀ m, (∀ k, k < m → P k) → P m) → ∀ n, P n  := by 
  intros IH n  
  have IH1 : ∀ p, p ≤ n → P p := by
    induction n with 
    | zero =>
      intros p H 
      cases H 
      apply IH 
      intros k Hk 
      cases Hk 
    | succ n' IHn' => 
      intros p H 
      apply IH
      intros k Hk 
      apply IHn' 
      omega 
  apply IH1 
  apply Nat.le_refl

/-
Essencialmente, o uso de relações bem formadas é uma 
generalização do princípio de indução forte para 
tipos de dados quaisquer.
-/

--
-- Acessibilidade de uma relação de ordem 

-- inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
-- | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
-- essencialmente, isso é o princípio de indução forte.

-- inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
-- | intro (h : ∀ a, Acc r a) : WellFounded r

lemma div_rec {n m : ℕ} : 0 < m ∧ m ≤ n → n - m < n := by 
  intros H1
  omega 

-- aqui explicitamente realizamos a chamada recursiva 
-- sobre um argumento menor e provamos esse fato usando 
-- div_rec 

def divF (n : ℕ)
         (f : (n' : Nat) → n' < n → ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n then
    f (n - m) (div_rec h) m + 1
  else
    0

def div1 := WellFounded.fix (measure id).wf divF

#check div1

-- outra maneira, é termos no escopo da definição 
-- uma prova mostrando que o argumento é menor e, 
-- partir disso, o compilador do Lean é capaz de 
-- automatizar o processo de construção do uso 
-- WellFounded.fix 

def div2 (n m : ℕ) : ℕ := 
  if h : 0 < m ∧ m ≤ n then 
    div2 (n - m) m + 1 
  else 0

lemma div2_def (n m : ℕ) 
  : div2 n m = if 0 < m ∧ m ≤ n then 
                  div2 (n - m) m + 1 else 0 := by 
  show div2 n m = _ 
  rw [div2]
  rfl 

lemma div_induction (P : ℕ → ℕ → Prop)
  (n m : ℕ)
  (IH : ∀ n m, 0 < m ∧ m ≤ n → P (n - m) m → P n m)
  (base : ∀ n m, ¬ (0 < m ∧ m ≤ n) → P n m) : P n m := 
  if h : 0 < m ∧ m ≤ n then 
    IH n m h (div_induction P (n - m) m IH base)
  else base n m h 


theorem div2_correct 
  : ∀ n m, ∃ q r, div2 n m = q ∧ n = m * q + r := by
    intros n m 
    induction n, m using div_induction with 
    | IH n m H IH => 
      rw [div2_def]
      split
      · 
        simp at * 
        rcases IH with ⟨ q, Heq ⟩ 
        exists q
        rw [ Nat.mul_add
           , Nat.mul_one
           , Nat.add_assoc _ m
           , Nat.add_comm m q
           , ← Nat.add_assoc _ q
           , ← Heq
           , ← Nat.sub_add_comm
           , Nat.add_sub_cancel]
        omega 
      · 
        contradiction
    | base n m H =>
      rw [div2_def]
      exists 0
      exists n
      split 
      contradiction 
      simp
 
-- Exercício: Defina uma função div3 que retorna o
-- quociente e o resto da divisão e prove a correção 
-- desta versão.

-- Exercício: Desenvolva uma função que realiza a 
-- intercalação de duas listas previamente ordenadas e 
-- prove que esta função preserva a relação de ordenação
-- das listas fornecidas como argumento.
