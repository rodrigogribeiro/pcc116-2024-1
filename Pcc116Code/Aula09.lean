
-- Aula 09. Sobrecarga e classes de tipos 

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

/-
# Classes de tipos

Classes de tipos foram introduzidas na linguagem Haskell
como uma forma de combinar polimorfismo paramétrico
(generics em C++ e Java) com sobrecarga.

De maneira intuitiva, uma classe de tipos é similar a
uma interface da linguagem Java: 
  - Especifica um nome para a classe e
  - Conjunto de operações que devem ser implementadas
    por tipos que são _instâncias_ desta classe.

A seguir, apresentamos um exemplo:
-/

class BoolEq (A : Type) where 
  beq : A → A → Bool 

/-
O trecho acima declara uma classe chamada BoolEq 
que possui como parâmetro um tipo A e uma operação 
beq de tipo A -> A -> Bool. 

Note que uma classe define apenas uma interface 
de um certo conjunto de tipos, chamados de 
instâncias. A seguir, apresentamos uma declaração
de instância. 
-/

def boolBEq (b1 b2 : Bool) : Bool :=
  match b1, b2 with 
  | true, true => true 
  | false, false => true 
  | _, _ => false
 

instance boolBoolEq : BoolEq Bool := {
  beq := boolBEq  
} 

def natBEq (n m : ℕ) : Bool := 
  match n, m with 
  | 0, 0 => true 
  | n' + 1, m' + 1 => natBEq n' m'
  | _, _ => false

instance natEq : BoolEq ℕ := {
  beq := natBEq 
}

-- definição de uma instância polimórfica 

instance prodEq {A B : Type}
                [BoolEq A][BoolEq B] : BoolEq (A × B) := {
  beq := λ p1 p2 => BoolEq.beq p1.1 p2.1 && 
                    BoolEq.beq p1.2 p2.2
} 


