-- Aula 11: Recursão geral 

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith 
import Mathlib.Data.Nat.Defs

-- ∀ {e}, ∃ r, f e = r
-- funções devem ser totais
-- * Recursão estrutural.
-- * Casamento de padrão exaustivo. 

-- definições parciais: uma maneira de contornar a 
-- exigência de totalidade

-- n ÷ m = (q,r) tal que n = m × q + r ∧ r < m  

partial def pdiv (n m : ℕ) : ℕ × ℕ := 
  match Nat.decLt n m with 
  | isTrue _ => (0, n)
  | _           => 
    match pdiv (n - m) m with
    | (q,r) => (q + 1, r)

-- Lean não identifica a chamada a pdif (n - m) m 
-- como seguindo uma cadeia decrescente finita de 
-- chamadas. Como resolver esse dilema?

-- Estratégia 1. uso de fuel
-- dois componentes:
-- * Contador de chamadas recursivas passado como argumento. 
-- * Resultado da forma Option A, em que A é o tipo do resultado. 
-- ** fuel = 0, resultado .none 
-- ** fuel ≠ 0, calcule o resultado fazendo chamada recursiva sobre fuel - 1
/-
inductive Decidable (P : Prop) : Type where 
| isTrue : P → Decidable P
| isFalse : ¬ P → Decidable P 

inductive Lt : ℕ → ℕ → Prop where 
| base : ∀ {m}, Lt 0 (m + 1)
| step : ∀ {n m}, Lt n m → Lt (n + 1) (m + 1)



def blt (n m : ℕ) : Bool := ... 

blt n m = true ∨  blt n m = false 

def decLt (n m : ℕ) : Decidable (Lt n m) := ...

if n < m then (0, n) else let (q,r) := div (n - m) m in (q + 1, r)
-/

inductive Lt : ℕ → ℕ → Prop where 
| base : ∀ {m}, Lt 0 (m + 1)
| step : ∀ {n m}, Lt n m → Lt (n + 1) (m + 1)

def blt (n m : ℕ) : Bool := 
  match n, m with 
  | 0, _ + 1 => true
  | 0, 0 => false 
  | _ + 1, 0 => false 
  | n + 1, m + 1 => blt n m

def ltDec (n m : ℕ) : Decidable (Lt n m) := 
  match n, m with 
  | 0, 0 => by 
      apply Decidable.isFalse 
      intros H 
      cases H 
  | 0, m + 1 => by 
      apply Decidable.isTrue 
      apply Lt.base 
  | n + 1, 0 => by 
    apply Decidable.isFalse 
    intros H 
    cases H 
  | n + 1, m + 1 => by
    have R : Decidable (Lt n m) := ltDec n m
    cases R with 
    | isFalse H => 
      apply Decidable.isFalse 
      intros H1 
      cases H1  
      contradiction
    | isTrue H =>
      apply Decidable.isTrue 
      apply Lt.step 
      exact H      

lemma test : Lt 2 5 := by 
  apply Lt.step 
  apply Lt.step 
  apply Lt.base 

def fuel_div_def (fuel : ℕ)(n m : ℕ) : Option (ℕ × ℕ) := 
  match fuel with 
  | 0 => .none 
  | fuel' + 1 => 
    match Nat.decLt n m with 
    | isTrue _ => .some (0,n)
    | _ => match fuel_div_def fuel' (n - m) m with 
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

-- Exemplo: < sobre ℕ
-- * n > ... > 0
-- < sobre ℤ não é bem formado.

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

-- ∀ n, P n ≃ P 0 ∧ ∀ n, P n → P (n + 1)

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
  omega -- Aritmética de Presburger

-- aqui explicitamente realizamos a chamada recursiva 
-- sobre um argumento menor e provamos esse fato usando 
-- div_rec 

def divF (n : ℕ)
         (f : (n' : Nat) → n' < n → ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n then
    f (n - m) (div_rec h) m + 1
  else
    0

def div1 n m := WellFounded.fix (measure id).wf divF n m

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

-- 3. Uso de um predicado de domínio 
-- Essa técnica consiste em definir um predicado que representa 
-- o domínio da função e então definimos a função por recursão 
-- sobre esse predicado.


inductive DivDom : ℕ → ℕ → Type where 
| Base1 : ∀ m, DivDom 0 (m + 1)
| Base2 : ∀ n, DivDom (n + 1) 1
| Step : ∀ {n m}, DivDom (n - m) m → DivDom n (m + 1) 

def div3F {n m} : DivDom n m → ℕ 
| DivDom.Base1 _ => 0 
| DivDom.Base2 n => n + 1 
| DivDom.Step Hrec => 
  div3F Hrec + 1 

-- tendo definido a função, o próximo passo é mostrar a totalidade do 
-- predicado para o domínio.

def divDom : ∀ (n m : ℕ), m ≠ 0 → DivDom n m
| 0, 0, Heq => by 
  simp at *
| 0, m + 1, _Heq => DivDom.Base1 m 
| n + 1, 1, _Heq => DivDom.Base2 n 
| n + 1, (m + 1) + 1, _Heq => by 
  apply DivDom.Step
  apply divDom 
  intros H 
  rcases H 

-- combinando a definição e totalidade do predicado 

def div3 (n m : ℕ)(H : m ≠ 0) : ℕ := 
  div3F (divDom n m H)


-- Exercício: Defina uma função div3 que retorna o
-- quociente e o resto da divisão e prove a correção 
-- desta versão.

-- Exercício: Desenvolva uma função que realiza a 
-- intercalação de duas listas previamente ordenadas e 
-- prove que esta função preserva a relação de ordenação
-- das listas fornecidas como argumento.


