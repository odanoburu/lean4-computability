namespace PRF

open Nat


inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

def Vector.get {α : Type u} : (as : Vector α n) → Fin n → α
  | cons a _,  ⟨0, _⟩ => a
  | cons _ as, ⟨Nat.succ i, h⟩ => get as ⟨i, Nat.le_of_succ_le_succ h⟩

def Vector.fromList {α : Type u} : (as : List α) → Vector α (List.length as)
  | [] => Vector.nil
  | x :: xs => Vector.cons x (Vector.fromList xs)

def enumeration {α : Type u} : Vector α n → (Fin n → α)
  | as => λ i => Vector.get as i

inductive PRF : Nat → Type where
  | zero    : PRF 0
  | succ    : PRF 1
  | proj    : {n : Nat} → Fin n → PRF n -- projection
  | comp    : {m k : Nat} → PRF m → (Fin m → PRF k) → PRF k -- composition
  | primrec : {n : Nat} → PRF n → PRF (n + 2) → PRF (n + 1) -- primitive recursion

--. composition:
-- If g is a function of m-variables and h₁ ... , hₘ are functions of k variables,
-- which are already defined, then composition yields the function
-- f(x) = g(h₁(x*),...,hₘ(x*))
--. primitive recursion:
-- f(0, x*) = g(x*)
-- f(n + 1, x*) = h(f(n, x*), n, x*)

def PRF.ToString : PRF n → String
  | PRF.zero => "zero"
  | PRF.succ => "succ"
  | PRF.proj {val := n, isLt := _} => s!"proj_{n}"
  | PRF.comp g _h => s!"{ToString g}∘"
  | PRF.primrec b c => s!"primrec({ToString b}, {ToString c})"

instance : ToString (PRF n) :=
  ⟨PRF.ToString⟩

def PRF.arity (_ : PRF a) : Nat := a

def finRangeAux : (m : Nat) → m < n → List (Fin n) → List (Fin n)
  | 0, zeroLTn, ns => {val := 0, isLt := zeroLTn} :: ns
  | succ m, succmLTn, ns =>
       let mLTn := Nat.lt_trans Nat.le.refl succmLTn
       finRangeAux m mLTn ({val := succ m, isLt := succmLTn} :: ns)

def finRange : (n : Nat) -> List (Fin n)
  | zero => []
  | succ n => finRangeAux n Nat.le.refl []

def List.lookupIdx : List α → Nat → Option α
  | [],    _   => none
  | a::_, 0   => some a
  | _::as, n+1 => lookupIdx as n

inductive EvalResult (α : Type u) where
  | outOfGas : EvalResult α
  | wrongNumberOfArguments (fn : String) (expected : Nat) (got : Nat) : EvalResult α
  | ok (val : α) : EvalResult α
  deriving Repr

export EvalResult (outOfGas wrongNumberOfArguments ok)

instance {α : Type u} [ToString α] : ToString (EvalResult α) :=
  ⟨fun r =>
  match r with
  | outOfGas => "Out of gas."
  | wrongNumberOfArguments fn expected got => s!"Wrong number of arguments for function {fn}: expected {expected} but got {got}"
  | ok r => s!"ok: {r}"⟩

def Nat.forEachUntil : (Nat → α → α) → Nat → α → α
| f, n, acc =>
  let rec helper : Nat → Nat → α → α
    | 0, _, acc => acc
    | n + 1, m, acc => helper n (m+1) (f m acc)
  helper n 0 acc

-- #eval Nat.forEachUntil (λ _ a => a + 1) 0 0
-- #eval Nat.forEachUntil (λ _ a => a + 1) 0 1
-- #eval Nat.forEachUntil Nat.add 10 1


def evaluate (gas : Nat) (f : PRF a) (ns : List Nat) : EvalResult Nat :=
  match gas with
  | zero => outOfGas
  | succ gas =>
         match f with
         | PRF.zero => ok 0
         | PRF.succ =>
                    match ns with
                    | List.cons n [] => ok (n + 1)
                    | _ => wrongNumberOfArguments "succ" 1 (List.length ns)
         | PRF.proj i =>
           match List.lookupIdx ns i with
           | some n => ok n
           | none => wrongNumberOfArguments "proj" i (List.length ns)
         | PRF.comp g hs =>
                    let mAs := List.foldr
                                (λ i acc =>
                                  match acc with
                                  | ok as =>
                                    match evaluate gas (hs i) ns with
                                    | ok a => ok <| a :: as
                                    | wrongNumberOfArguments fn expected got => wrongNumberOfArguments fn expected got
                                    | outOfGas => outOfGas
                                  | err => err)
                                (ok [])
                                (finRange <| PRF.arity g)
                    match mAs with
                    | ok as => evaluate gas g as
                    | outOfGas => outOfGas
                    | wrongNumberOfArguments fn expected got => wrongNumberOfArguments fn expected got
         | PRF.primrec g h =>
           match ns with
           | [] => wrongNumberOfArguments "primrec" 1 0
           | n :: ns =>
             Nat.forEachUntil
               (λ n acc =>
                 match acc with
                 | outOfGas => outOfGas
                 | wrongNumberOfArguments fn expected got => wrongNumberOfArguments fn expected got
                 | ok fn => evaluate gas h (fn :: n :: ns))
               n
               (evaluate gas g ns)

def PRF.comp1 : PRF 1 → PRF k → PRF k
  | g, h => PRF.comp g (λ _ => h)

def PRF.comp2 : PRF 2 → PRF k → PRF k → PRF k
  | g, h, i =>
    PRF.comp
      g
      (λ n =>
        match n with
        | {val := 0, isLt := _} => h
        | {val := 1, isLt := _} => i
        | {val := n + 2, isLt} => by contradiction)

def PRF.identity : PRF 1 := PRF.proj 0

def PRF.first : PRF (n + 1) := PRF.proj 0

def PRF.second : PRF (n + 2) := PRF.proj 1

def PRF.third : PRF (n + 3) := PRF.proj 2

def PRF.fourth : PRF (n + 4) := PRF.proj 3

def PRF.const {k : Nat} : Nat → PRF k
  | 0 =>
      PRF.comp PRF.zero (λ {isLt := zeroltzero} =>
                           by contradiction)
  | n+1 =>
      PRF.comp1 PRF.succ (@PRF.const k n)

def PRF.add : PRF 2 :=
  PRF.primrec
    PRF.identity
    (PRF.comp1 PRF.succ PRF.first)

-- #eval evaluate 1000 PRF.add [3, 2]

def PRF.mul : PRF 2 :=
  PRF.primrec
    (PRF.const 0)
    (PRF.comp2 PRF.add (PRF.proj 0) (PRF.proj 2))

-- #eval evaluate 1000 PRF.mul [3, 0]
-- #eval evaluate 1000 PRF.mul [3, 4]

def PRF.exp : PRF 2 :=
  PRF.comp2
    (PRF.primrec
      (PRF.const 1)
      (PRF.comp2 PRF.mul PRF.first (PRF.proj 2)))
    PRF.second
    PRF.first

-- #eval evaluate 100000000 PRF.exp [0, 0]
-- #eval evaluate 100000000 PRF.exp [0, 1]
-- #eval evaluate 100000000 PRF.exp [10, 0]
--#eval evaluate 100000000 PRF.exp [10, 2]

def PRF.pred : PRF 1 :=
  PRF.primrec (PRF.const 0) PRF.second

-- #eval evaluate 100000000 PRF.pred [2]

def PRF.signal : PRF 1 :=
  PRF.primrec
    (PRF.const 0)
    (PRF.const 1)

-- #eval evaluate 100 PRF.signal [0]
-- #eval evaluate 100 PRF.signal [1]
-- #eval evaluate 100 PRF.signal [20]

def PRF.le : PRF 2 :=
  PRF.comp1 PRF.signal
    (PRF.primrec
      (PRF.comp1 PRF.succ PRF.first)
      (PRF.comp1 PRF.pred PRF.first))

-- #eval evaluate 100 PRF.le [9, 10]
-- #eval evaluate 100 PRF.le [10, 10]
-- #eval evaluate 100 PRF.le [2, 1]

def PRF.lt : PRF 2 :=
  PRF.comp2 PRF.le (PRF.comp1 PRF.succ PRF.first) PRF.second

--#eval evaluate 100 PRF.lt [9, 10]
--#eval evaluate 100 PRF.lt [10, 10]
--#eval evaluate 100 PRF.lt [2, 1]

def PRF.not : PRF 1 :=
  PRF.primrec
    (PRF.const 1)
    (PRF.const 0)

def PRF.if : PRF k → PRF k → PRF k → PRF k
  | t, f, g =>
    PRF.comp2
      PRF.add
      (PRF.comp2 PRF.mul (PRF.comp1 PRF.signal t) f)
      (PRF.comp2 PRF.mul (PRF.comp1 PRF.not t) g)

-- #eval evaluate 10 (PRF.if PRF.first PRF.first PRF.not) [0]

def PRF.and : PRF 2 :=
  PRF.comp1 PRF.signal (PRF.if PRF.first PRF.second (PRF.const 0))

-- #eval evaluate 100 PRF.and [2, 0]

def PRF.fixFirst : PRF k → PRF (k + 1) → PRF k
  | z, f =>
    PRF.comp
      f
      (λ {val := n, isLt := nLt} =>
        match n with
        | 0 => z
        | n + 1 => PRF.proj {val := n, isLt := Nat.le_of_succ_le_succ nLt
        })

def PRF.dropFirst : PRF k → PRF (k + 1)
  | f =>
    PRF.comp
      f
      (λ {val := i, isLt := iLt} =>
        PRF.proj { val := i + 1
                 , isLt := Nat.succ_le_succ iLt
                 })

def PRF.mapNth : Nat → PRF k → PRF k → PRF k
  | i, g, f =>
    PRF.comp
      f
      (λ {val := n, isLt := nLt} =>
        if n = i
        then g
        else PRF.proj {val := n, isLt := nLt})

def PRF.firstLEsat : PRF (k + 1) → PRF k → PRF k
-- finds first number less or equal than first input argument that
-- satisfies predicate p
  | p, g =>
    -- we recurse on the first argument, when an index i has p(i,
    -- x₂, …, xₙ) > 0 we return i + 1; at the top-level we take
    -- pred, so we have 0 for failure and i + 1 for success with
    -- index i
    PRF.comp1
      PRF.pred
      (PRF.fixFirst g
      (PRF.primrec
        (PRF.comp1
          PRF.signal
          (PRF.fixFirst
            (PRF.const 0)
            p))
        (PRF.if
          PRF.first
          PRF.first
          (PRF.if
            (PRF.dropFirst (PRF.mapNth 0 (PRF.comp1 PRF.succ PRF.first) p))
            (PRF.comp1 PRF.succ <| PRF.comp1 PRF.succ PRF.second)
            (PRF.const 0)))))

--#eval evaluate 1000 (@PRF.firstLEsat 0 (PRF.comp2 PRF.le (PRF.const 5) PRF.first) (PRF.const 10)) [1]

def PRF.anyLEsat : PRF 1 → PRF 1
-- anyLEsat(p, n) = { 1 if p(i) for some i <= n; 0 otherwise}
  | p =>
    (PRF.primrec
      (PRF.comp1 PRF.signal (PRF.comp1 p (PRF.const 0)))
      (PRF.if
        PRF.first
        PRF.first
        (PRF.if
          (PRF.comp1 p (PRF.comp1 PRF.succ PRF.second))
          (PRF.const 1)
          PRF.first)))

--#eval evaluate 1000 (PRF.anyLEsat (PRF.comp2 PRF.le (PRF.const 3) PRF.first)) [2]

def PRF.limMin : PRF (k + 1) → PRF k → PRF k
  -- (μ z ≤ g(x₁, ..., xₙ))[h(z, x₁, ..., xₙ) > 0]
  | h, g => PRF.firstLEsat h g

-- #eval evaluate
--         1000
--         (PRF.limMin
--           (PRF.comp2 PRF.le (PRF.const 3) PRF.first)
--           (@PRF.comp2 1 PRF.add PRF.first (PRF.const 1)))
--         [2]

namespace TM

def TM.len : Nat → PRF 1
  -- lenₖ(w) = z such that k^z > w and ∀n, k^n > w → n > z
  | k =>
    PRF.limMin
      (PRF.comp2 PRF.lt PRF.second (PRF.comp2 PRF.exp (PRF.const k) PRF.first))
      PRF.identity

--#eval evaluate 100000 (TM.len 10) [10]

def TM.concat : Nat → PRF 2
-- w₁.w₂ = w₁*k^len(w₂) + w₂
  | k =>
    PRF.comp2
      PRF.add
      (PRF.comp2
        PRF.mul
        PRF.first
        (PRF.comp2
          PRF.exp
          (PRF.const k)
          (PRF.comp1 (TM.len k) PRF.second)))
      PRF.second

--#eval evaluate 100000 (TM.concat 10) [1, 2]

-- def TM.pre : Nat → PRF 2
--   -- pre(w₁, w) = z s.t. ∃z,∃i, z.w₁.i = w
--   | k => PRF.limMin (PRF.firstLEsat (PRF.comp2 (TM.concat k) _ _)) PRF.second

end TM
end PRF


open PRF.TM
def main : IO Unit :=
  IO.println s!"{PRF.evaluate 100000 (TM.len 10) [10]}"
