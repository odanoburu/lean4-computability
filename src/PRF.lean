namespace PRF

open Nat


inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

def Vector.get {α : Type u} : (as : Vector α n) → Fin n → α
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

-- inductive PR : (Vector Nat n → Nat) → Prop
--   | zero : PR (λ _ => 0)
--   | succ : PR (λ ns : Vector Nat 1 =>
--                  match ns with
--                  | Vector.cons n Vector.nil => n + 1)
--  | proj : PR

inductive PRF : Nat → Type where
  | zero : PRF 0
  | succ : PRF 1
  | proj : {n : Nat} → Fin n → PRF n
  | comp : {m k : Nat} → PRF m → (Fin m → PRF k) → PRF k

def PRF.arity (_ : PRF a) : Nat := a

-- If g is a function of m-variables and h₁ ... , hm are functions of k variables,
-- which are already defined, then composition yields the function
-- f(x) = g(h₁(x*),...,hm(x*))

def finRangeAux : (m : Nat) → m < n → List (Fin n) → List (Fin n)
  | 0, _, ns => ns
  | succ m, succmLTn, ns =>
       let mLTn := Nat.lt_trans Nat.le.refl succmLTn
       finRangeAux m mLTn ({val := m, isLt := mLTn} :: ns)

def finRange : (n : Nat) -> List (Fin n)
  | zero => []
  | succ n => finRangeAux n Nat.le.refl []

def evaluate (gas : Nat) (f : PRF a) (ns : Vector Nat a) : Option Nat :=
  match gas with
  | zero => none
  | succ gas =>
         match f with
         | PRF.zero => some 0
         | PRF.succ =>
                    match ns with
                    | Vector.cons n Vector.nil => some (n + 1)
         | PRF.proj i => some (Vector.get ns i)
         | PRF.comp g hs =>
                    let as := List.foldr
                                (λ i acc => match acc with
                                            | none => none
                                            | some rs => match evaluate gas (hs i) ns with
                                                         | none => none
                                                         | some r => some <| Vector.cons r rs)
                                (some Vector.nil)
                                (finRange (PRF.arity g))
                    match as with
                    | none => none
                    | some as => evaluate gas g as
