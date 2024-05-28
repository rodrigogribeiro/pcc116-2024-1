-- Aula 08: Programando com tipos dependentes 

import Mathlib.Data.Nat.Defs

-- considere as seguintes função sobre lista 

def listHead {A : Type}(xs : List A) : Option A := 
  match xs with 
  | [] => none 
  | x :: _ => some x 

-- head : List A -> A 
-- parcial. 
-- totais! 
/-
inductive Option (A : Type) where 
| none : Option A 
| some : A → Option A 

exceptions are bad! exceptions = goto 
-/


-- problema: inconveniente, pois isso obriga a clientes 
-- a realizar casamento de padrão sobre um valor de tipo 
-- Option 

def foo (xs : List ℕ) : ℕ := 
  match listHead xs with 
  | none => 0 
  | some x => x 

-- como determinar se um "0" retornado é o primeiro elemento 
-- ou apenas um valor de erro?

-- Como evitar que a função head seja chamada sobre listas 
-- vazias?

-- Solução: fazer o tamanho da lista ser parte do tipo 
-- problema: definição da adição da Mathlib é feita sob
-- o segundo argumento. 

def plus (n m : ℕ) : ℕ := 
  match n with 
  | 0 => m 
  | n' + 1 => Nat.succ (plus n' m)  

lemma plus_add (n m : ℕ) : n + m = plus n m := by 
  induction n with 
  | zero =>
    simp [plus]
  | succ n' IH =>
    simp [plus, Nat.succ_add, IH]

inductive Vec (A : Type) : ℕ → Type where 
| nil  : Vec A 0 
| cons : ∀ {n}, A → Vec A n → Vec A (plus 1 n)
deriving Repr 

def ex1 : Vec ℕ 0 := Vec.nil 
def ex2 : Vec ℕ 1 := Vec.cons 1 ex1 
def ex3 : Vec ℕ 3 := Vec.cons 3 (Vec.cons 2 ex2)

-- resulta em erro 

-- def ex4 : Vec ℕ 3 := ex2

section VEC 
  variable {A : Type}

  -- safe head 

  def vhead {n : ℕ}(v : Vec A (n + 1)) : A := 
     match v with 
     | Vec.cons x _ => x  
  -- aqui o Lean é capaz de determinar que não é possível  
  -- usar o construtor nil
  -- ∀ n x, length (replicate n x) = n
  -- correta por construção 

  def vreplicate (n : ℕ)(x : A) : Vec A n := 
    match n with 
    | 0 => Vec.nil 
    | n + 1 => Vec.cons x (vreplicate n x)

  def toList {n}(xs : Vec A n) : List A := 
    match xs with 
    | Vec.nil => [] 
    | Vec.cons x xs => x :: (toList xs)

def vapp {n m : ℕ}(xs : Vec A n)(ys : Vec A m) 
  : Vec A (plus n m) :=
  match xs with 
  | Vec.nil => ys 
  | Vec.cons z zs => Vec.cons z (vapp zs ys)


-- zipping two lists 

def zipp {A B : Type}
  (xs : List A)(ys : List B) : List (A × B) :=
  match xs, ys with 
  | [], _ => [] 
  | _ , [] => [] 
  | x :: xs, y :: ys => (x,y) :: zipp xs ys 

def Vec.zip {A B : Type}{n} 
  (xs : Vec A n)(ys : Vec B n) : Vec (A × B) n := 
  match xs, ys with 
  | Vec.nil , Vec.nil => Vec.nil 
  | Vec.cons x xs, Vec.cons y ys => 
    Vec.cons (x,y) (Vec.zip xs ys)

-- lookup function 

inductive fin : ℕ → Type where 
| zero : ∀ {n}, fin (n + 1)
| succ : ∀ {n}, fin n → fin (n + 1)


def Vec.lookup {A n}(xs : Vec A n)(idx : fin n) : A := 
  match idx, xs with 
  | fin.zero, Vec.cons x _ => x 
  | fin.succ idx, Vec.cons _ xs => Vec.lookup xs idx

-- another application: universe pattern 

inductive NatOrBool : Type where 
| nat | bool 

abbrev NatOrBool.asType (code : NatOrBool) : Type := 
  match code with 
  | .nat => ℕ 
  | .bool => Bool 

def decode (ty : NatOrBool)
           (input : String) : Option ty.asType :=
  match ty with 
  | .nat => String.toNat? input 
  | .bool => 
    match input with 
    | "true" => .some true 
    | "false" => .some false 
    | _ => .none

#eval decode .nat "123"

-- a universe for finite types 

inductive Finite : Type where 
| unit   : Finite 
| either : Finite → Finite → Finite 
| pair   : Finite → Finite → Finite 

abbrev Finite.asType : Finite → Type 
| .unit => Unit 
| .either t1 t2 => asType t1 ⊕ asType t2  
| .pair t1 t2 => asType t1 × asType t2 

def Finite.beq (t : Finite)(x y : t.asType) : Bool := 
  match t with 
  | .unit => true 
  | .either t1 t2 => 
    match x, y with 
    | Sum.inl a, Sum.inl b => beq t1 a b 
    | Sum.inr a, Sum.inr b => beq t2 a b 
    | _ , _ => false 
  | .pair t1 t2 => 
    beq t1 x.fst y.fst && beq t2 x.snd y.snd 

-- data universe 

inductive U : Type where 
| bit | char | nat | vec : U → ℕ → U 

abbrev U.asType : U → Type 
| .bit => Bool 
| .char => Char 
| .nat => ℕ 
| .vec u n => Vec u.asType n

def parens : String → String
| s => "(" ++ s ++ ")"

def asString {u : U} (v : u.asType) : String := 
  match u, v with 
  | .bit, true => "true"
  | .bit, false => "false"
  | .char, c => c.toString
  | .nat, n => n.repr 
  | .vec _ 0, Vec.nil => "nil"
  | .vec u (n + 1), Vec.cons x xs => 
    parens (asString x) ++ " :: " ++ 
    parens (@asString (.vec u n) xs)

-- exercícios:

-- Defina uma função que conta o número de elementos 
-- de um tipo finito definido utilizando o universo 
-- finite. Note que o código either representa a união 
-- e o pair o produto cartesiano de valores.

def Finite.size (t : Finite) : ℕ := sorry

-- Defina uma função que teste a igualdade valores 
-- definidos utilizando o universo U 

def U.beq (t : U)(x y : t.asType) : Bool := sorry 
