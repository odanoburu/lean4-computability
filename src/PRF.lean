namespace PRF

open Nat


inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

structure IList (α : Type u) (n : Nat) where
  val  : List α
  size : List.length val = n

def Vector.get {α : Type u} : (as : Vector α n) → Fin n → α
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

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

@[simp] theorem rangeSizeIsN : ∀ (n : Nat), List.length (finRange n) = n := sorry
--   | 0 =>
--     calc
--       List.length (finRange 0)
--         = List.length [] := by rw [finRange]
--       _ = 0 := by rfl
--   | succ n =>
--     calc
--       List.length (finRange (succ n))
--         = succ (List.length (finRange n)) := by rw [_]
--       _ = succ n := _

def IListFinRange : (n : Nat) → IList (Fin n) n
  | n => { val := finRange n, size := rangeSizeIsN n}

def List.lookupIdx : List α → Nat → Option α
  | [],    _   => none
  | a::_, 0   => some a
  | _::as, n+1 => lookupIdx as n

def evaluate (gas : Nat) (f : PRF a) (ns : List Nat) : Option Nat :=
  match gas with
  | zero => none
  | succ gas =>
         match f with
         | PRF.zero => some 0
         | PRF.succ =>
                    match ns with
                    | List.cons n [] => some (n + 1)
                    | _ => none
         | PRF.proj i => List.lookupIdx ns i
         | PRF.comp g hs =>
                    let mAs := List.foldr
                                (λ i acc =>
                                  match acc with
                                  | none => none
                                  | some as =>
                                    match evaluate gas (hs i) ns with
                                    | none => none
                                    | some a => some <| a :: as)
                                (some [])
                                (finRange (PRF.arity g))
                    match mAs with
                    | none => none
                    | some as => evaluate gas g as

#eval List.range 1
