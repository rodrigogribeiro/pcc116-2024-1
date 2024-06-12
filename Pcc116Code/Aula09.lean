
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

-- sobrecarga. 
-- Diferentes tipos de polimorfismo na linguagem
---- Inclusão (herança)
---- paramétrico (generics / templates)
---- sobrecarga (independente de contexto)
------- Tipos de retorno não podem ser sobrecarregados de forma 
------- arbitrária
------- Integer.parseInt, Float.parseFloat...
------- String -> Int   , String -> Float 
-------- parse :: String -> a
---- sobrecarga dependente de contexto 
------ a escolha da implementação não depende somente do 
------- tipo dos argumentos mas também de onde o resultado
------- é usado.
------- read :: String -> a 
------- \ x -> read x && True 
------- && :: Bool -> Bool -> Bool 
------- True :: Bool 
------- read x :: Bool 
------- x :: String 
------- read :: String -> Bool 
-------- \ x -> read x + 1 :: Int  
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

-- definição de uma instância polimórfica p.1, p.2  
-- ∀ A, A → A polimórfico. 

instance prodEq {A B : Type}
                [BoolEq A][BoolEq B] -- restrições 
          : BoolEq (A × B) := {
  beq := λ p1 p2 => BoolEq.beq p1.1 p2.1 && 
                    BoolEq.beq p1.2 p2.2
} 

-- sobrecarga de literais 

inductive Pos : Type where
| one : Pos 
| succ : Pos → Pos 
deriving Repr 

class Plus (A : Type) where 
  plus : A → A → A 

instance natPlus : Plus ℕ := {
  plus := Nat.add 
}

-- addition over Pos 

def Pos.plus (x y : Pos) : Pos := 
  match x with 
  | one => Pos.succ y 
  | succ x1  => Pos.succ (plus x1 y)

instance posPlus : Plus Pos := {
  plus := Pos.plus
}

-- Adição da biblioteca é definida pela classe Add 

instance posAdd : Add Pos := {
  add := Pos.plus
}

-- pergunta: como usar números para valores de tipo Pos?

-- class OfNat (A : Type)(n : ℕ) where 
--   ofNat : A 

-- ℕ = {0, 1, 2, ... 
-- P = {1, 2, 3, ...

def natPlusOne : ℕ → Pos 
| 0 => Pos.one 
| n + 1 => Pos.succ (natPlusOne n)

instance : OfNat Pos (n + 1) where 
  ofNat := natPlusOne n

#eval Pos.plus 1 2

-- # Efeitos colaterais e mônadas

-- Considere a tarefa de implementar uma função 
-- para somar o segundo, o quarto e sétimo elementos
-- de uma lista de números naturais

-- obtendo o nth elemento 

def nth {A : Type} : List A → ℕ → Option A 
| [], _ => .none 
| x :: _, 0 => .some x
| _ :: xs, n + 1 => nth xs n 

-- usando nth, podemos definir a função
def sum247 (xs : List ℕ) : Option ℕ := 
  match nth xs 1 with 
  | .some n2 => 
    match nth xs 3 with 
    | .some n4 => 
      match nth xs 6 with 
      | .some n7 => .some (n2 + n4 + n7)
      | .none => .none 
    | .none => .none 
  | .none => .none 

-- problemas: código poluído por casamento de padrão
--            repetição, caso que resulta em none 
-- solução: abstrair o padrão 

def connect {A B : Type} : Option A → (A → Option B) → Option B 
| .none, _ => .none 
| .some x, f =>  f x


-- definição de sum247 usando connect 

def sum247Connect (xs : List ℕ) : Option ℕ := 
  connect (nth xs 1)
    (λ x2 => connect (nth xs 3)
                (λ x4 => connect (nth xs 6)
                           (λ x7 => .some (x2 + x4 + x7))))

-- definição de sum247 usando bind (definido na biblioteca)

def sum247Bind (xs : List ℕ) : Option ℕ :=
  bind (nth xs 1)
    (λ x2 => bind (nth xs 3)
               (λ x4 => bind (nth xs 6)
                      (λ x7 => pure (x2 + x4 + x7))))


-- definição usando o operador para bind 

def sum247Op (xs : List ℕ) : Option ℕ := 
  nth xs 1 >>= λ x2 => 
    nth xs 3 >>= λ x4 => 
      nth xs 6 >>= λ x7 => 
      pure (x2 + x4 + x7)

-- definição usando do syntax sugar. Do notation  

def sum247Do (xs : List ℕ) : Option ℕ := 
  do 
    let x2 ← nth xs 1 -- nth xs 1 >>= λ x2 => ...  
    let x4 ← nth xs 3 
    let x7 ← nth xs 6 
    pure (x2 + x4 + x7)

#eval sum247 (List.replicate 5 1)

/-
# Mônadas

Uma mônada é um construtor de tipos m :: Type → Type 
que possui duas operações:

pure {A : Type} : A → m A 
bind {A B : Type} : m A → (A → m B) → m B

Normalmente, o bind é representado pelo operador >>= 
e a notação é válida para qualquer tipo que implemente
as classes Pure e Bind 

class Pure (m : Type → Type) where 
  pure {A : Type} : A → m A 

class Bind (m : Type → Type) where 
  bind {A B : Type} : m A → (A → m B) → m B

e três propriedades: 

1. pure a >>= f     ≃ f a 
2. ma >>= pure      ≃ ma  
3. (ma >>= f) >>= g ≃ (ma >>= λ a => f a >>= g)

Mônadas são usadas para representar diferentes 
efeitos colaterais. Veremos alguns exemplos. 
-/

inductive Reader (R A : Type) : Type where 
| MkReader : (R → A) → Reader R A 

def Reader.runReader : Reader R A → R → A 
| (Reader.MkReader f) , r => f r

def Reader.pure {R A : Type} : A → Reader R A 
| x => Reader.MkReader (λ _ => x)

def Reader.bind {R A B : Type}
                (ma : Reader R A)
                (f : A → Reader R B) : Reader R B := 
  Reader.MkReader (λ r => 
      let a := Reader.runReader ma r
      let rb := f a 
      Reader.runReader rb r)

instance {R : Type} : Pure (Reader R) where 
  pure := Reader.pure 

instance {R : Type} : Bind (Reader R) where 
  bind := Reader.bind 

-- consultando a variável de leitura 

def ask {R : Type} : Reader R R :=
  Reader.MkReader (λ r => r)

-- exemplo: expressões com variáveis 

inductive Expr : Type where 
| Var : String → Expr 
| Con : ℕ → Expr 
| Add : Expr → Expr → Expr 
deriving Repr 

-- environment => Memória 

def Env := List (String × ℕ)

-- interpretação usando mônada Reader 
#check List.lookup 

def evalR : Expr → Reader Env ℕ 
| Expr.Var s => do 
    let env ← ask 
    match List.lookup s env with 
    | .some n => pure n 
    | .none => pure 0 
| Expr.Con n => pure n 
| Expr.Add e1 e2 => do 
  let v1 ← evalR e1 
  let v2 ← evalR e2 
  pure (v1 + v2)

-- execução 

def eval : Env → Expr → ℕ 
| env, e => Reader.runReader (evalR e) env

def env : Env := [("x", 2), ("y", 5)]

open Expr 

def exp : Expr := Add (Var "x") (Add (Var "y") (Con 3))

#eval eval env exp

-- mônada de estado 

inductive State (S A : Type) : Type where 
| MkState : (S → (A × S)) → State S A 

def State.runState {S A : Type} 
  : State S A → S → (A × S) 
| (State.MkState f) => f

def State.pure {S A : Type} : A → State S A 
| x => State.MkState (λ s => (x , s))

instance {S : Type} : Pure (State S) where 
  pure := State.pure 

def State.bind {S A B : Type} : 
  State S A → (A → State S B) → State S B 
| sa , f => State.MkState (λ s => 
      let r := State.runState sa s 
      State.runState (f r.1) r.2)

instance : Bind (State S) where 
  bind := State.bind

-- operações da mônada de estado 

def put {S : Type} : S → State S Unit 
| x => State.MkState (λ _ => (() , x)) 

def get {S : Type} : State S S := 
  State.MkState (λ s => (s, s))

-- exemplo comandos. 

inductive Stmt : Type where 
| Assign : String → Expr → Stmt 
| Print : Expr → Stmt 
| Seq : Stmt → Stmt → Stmt 
| Nop : Stmt 

def Log : Type := List String 

def lookupVar : String → State (Env × Log) ℕ 
| v => do 
  let s ← get 
  match List.lookup v s.1 with 
  | .some n => pure n 
  | _ => pure 0 

def updateVar : String → ℕ → State (Env × Log) Unit 
| s , n => do 
  let p ← get 
  put ((s, n) :: p.1, p.2)

def writeLog : ℕ → State (Env × Log) Unit 
| n => do 
  let p ← get 
  put (p.1, toString n :: p.2)

def evalExp : Expr → State (Env × Log) ℕ 
| Expr.Con n => pure n 
| Expr.Add e1 e2 => do 
  let n1 ← evalExp e1 
  let n2 ← evalExp e2 
  pure (n1 + n2)
| Expr.Var v => lookupVar v 

def evalStmt : Stmt → State (Env × Log) Unit
| Stmt.Nop => pure Unit.unit
| Stmt.Seq s1 s2 => do 
  evalStmt s1 
  evalStmt s2
| Stmt.Assign s e => do 
  let v ← evalExp e 
  updateVar s v
| Stmt.Print e => do 
  let v ← evalExp e 
  writeLog v

def evalProg : Stmt → (Env × Log)
| s => 
  let res := State.runState (evalStmt s) ([], [])
  res.2 

-- outro exemplo de mônada: IO 

