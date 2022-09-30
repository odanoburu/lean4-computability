open Nat

structure Vector (n : Nat) (α : Type u) where
  val  : List α
  hasLen : List.length val = n

@[specialize] def Vector.get {α : Type u} : (as : Vector n α) → Fin n → α
  | xs, {val := i, isLt} =>
    -- List.length xs.val = n, n <= n → n <= List.length xs.val
    List.get xs.val {val := i, isLt := Nat.le_trans isLt (Eq.subst (Eq.symm xs.hasLen) Nat.le.refl)}

def Vector.fromList {α : Type u} : (as : List α) → Vector (List.length as) α
  | xs => {val := xs, hasLen := rfl}

-- @[specialize] def Vector.cons {α : Type u} : α → Vector n α → Vector (n + 1) α
--   | x, {val := xs, hasLen} =>
--     let consLen : List.length (x :: xs) = List.length xs + 1 := List.length_cons x xs
--     {val := x :: xs, hasLen := @Eq.subst _ (λ sm => List.length (x :: xs) = sm + 1) _ _ hasLen consLen}

def Vector.enumeration {α : Type u} : Vector n α → (Fin n → α)
  | as => λ i => Vector.get as i

-- @[specialize] def List.build {α : Type u} (n : Nat) (f : Fin (n + 1) → α) : List α :=
--   let rec helper : Fin (n + 1)  → List α → List α
--     | {val := 0, isLt := _}, acc => (f {val := 0, isLt := Nat.zero_lt_succ n} :: acc)
--     | {val := i + 1, isLt := succ_i_lt_n}, acc =>
--       let i_lt_succ_n := Nat.lt_trans Nat.le.refl succ_i_lt_n
--       helper {val := i, isLt := i_lt_succ_n} (f {val := i + 1, isLt := succ_i_lt_n} :: acc)
--   helper {val := n, isLt := Nat.le.refl} []

-- @[simp] theorem List.length_build {α} (n : Nat) {f : Fin (n + 1) → α} : Eq (List.build n f).length (n + 1) := by
--   induction n with
--   | zero => rfl
--   | succ n => sorry

-- @[specialize] def Vector.build {α : Type u} (n : Nat) (f : Fin (n + 1) → α) : Vector (n + 1) α :=
--   {val := (List.build n f), hasLen := List.length_build n}

namespace PRF
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

def evaluate (f : PRF a) (arg : Fin a → Nat) : Nat :=
  match f with
  | PRF.zero => 0
  | PRF.succ => arg 0 + 1
  | PRF.proj i => arg i
  | PRF.comp g hs => evaluate g (λ i => evaluate (hs i) arg)
  | PRF.primrec g h =>
    let evalG := evaluate g
    let evalH := evaluate h
    let rec primrec : Nat → Nat
    | 0 =>
      evalG
        (λ {val := i, isLt := i_lt_n} =>
          arg {val := i + 1, isLt := Nat.succ_le_succ i_lt_n})
    | n + 1 =>
      evalH
        (λ fini =>
          match fini with
          | {val := 0, isLt := _} => primrec n
          | {val := 1, isLt := _} => n
          | {val := i + 2, isLt} => arg {val := i + 1, isLt := Nat.pred_le_pred isLt})
    primrec (arg 0)

def eval (f : PRF n) (args : Vector n Nat) : Nat :=
  evaluate f (Vector.enumeration args)

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

def PRF.comp3 : PRF 3 → PRF k → PRF k → PRF k → PRF k
  | g, h, i, j =>
    PRF.comp
      g
      (λ n =>
        match n with
        | {val := 0, isLt := _} => h
        | {val := 1, isLt := _} => i
        | {val := 2, isLt := _} => j
        | {val := n + 3, isLt} => by contradiction)

def PRF.comp4 : PRF 4 → PRF k → PRF k → PRF k → PRF k → PRF k
  | g, h, i, j, l =>
    PRF.comp
      g
      (λ n =>
        match n with
        | {val := 0, isLt := _} => h
        | {val := 1, isLt := _} => i
        | {val := 2, isLt := _} => j
        | {val := 3, isLt := _} => l
        | {val := n + 4, isLt} => by contradiction)

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

def PRF.or : PRF 2 :=
  PRF.comp1 PRF.signal (PRF.comp2 PRF.add PRF.first PRF.second)

def PRF.and : PRF 2 :=
  PRF.comp2 PRF.mul (PRF.comp1 PRF.signal PRF.first) (PRF.comp1 PRF.signal PRF.second)

-- #eval evaluate 100 PRF.and [2, 0]

def PRF.eq : PRF 2 :=
  PRF.comp2
    PRF.and
    PRF.le
    (PRF.comp2 PRF.le PRF.second PRF.first)

--#eval evaluate 100000 PRF.eq [0, 1]
--#eval evaluate 100000 PRF.eq [11, 11]
--#eval evaluate 100000 PRF.eq [2, 1]

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

def PRF.dropNth : Nat → PRF k → PRF (k + 1)
  | n, f =>
    PRF.comp
      f
      (λ {val := i, isLt := iLt} =>
        if i < n
        then
        PRF.proj { val := i, isLt := Nat.le.step iLt }
        else
        PRF.proj { val := i + 1
                 , isLt := Nat.succ_le_succ iLt
                 })

--#eval evaluate 100 (PRF.dropNth 0 PRF.le) [4, 5 , 3]

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

def PRF.disjunction : PRF (k + 1) → PRF (k + 1)
-- disjunction(p, n, x₁, ..., xₙ) = { 1 if p(i, n, x₁, ..., xₙ) for some i <= n; 0 otherwise}
  | p =>
    PRF.comp2
      PRF.or
      (PRF.primrec
        (PRF.const 0)
        (PRF.if
          PRF.first
          PRF.first
          (PRF.comp1 PRF.signal
            (PRF.dropNth 0 p))))
      p

--#eval evaluate 1000 (@PRF.disjunction 0 (PRF.comp2 PRF.le (PRF.const 13) PRF.first)) [0]

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

def k : Nat
  -- number of symbols in the alphabet
  := 10

def symbolMark : Nat
  -- mark before a symbol starts
  := 2

def stateMark : Nat
  -- mark before a state starts
  := 3

def movementMark : Nat
  -- mark before a movement
  := 4

def leftMark : Nat
  -- indicates left movement
  := 5

def rightMark : Nat
  -- indicates right movement
  := 6

def stopMark : Nat
  -- indicates stop (non-)movement
  := 7

def stepMark : Nat
  -- separates a TM step from another
  := 8

def emptyMark : Nat
  -- denotes the empty cell
  := 9

def TM.len : PRF 1 :=
  -- lenₖ(w) = z such that k^z > w and ∀n, k^n > w → n > z
  PRF.limMin
    (PRF.comp2 PRF.lt PRF.second (PRF.comp2 PRF.exp (PRF.const k) PRF.first))
    PRF.identity

#eval eval TM.len (Vector.fromList [10])

def TM.concat : PRF 2 :=
  -- w₁.w₂ = w₁*k^len(w₂) + w₂
  PRF.comp2
    PRF.add
    (PRF.comp2
      PRF.mul
      PRF.first
      (PRF.comp2
        PRF.exp
        (PRF.const k)
        (PRF.comp1 len PRF.second)))
    PRF.second

--#eval evaluate 100000 (TM.concat 10) [1, 1]

def TM.pre : PRF 2 :=
  -- pre(w₁, w) = z s.t. ∃z,∃i, z.w₁.i = w
  PRF.limMin
    (PRF.comp4
      (PRF.disjunction
        (PRF.comp2
          PRF.eq
          PRF.fourth /- w -/
          (PRF.comp2 concat PRF.second (PRF.comp2 concat PRF.third PRF.first))))
      PRF.third /- w -/
      PRF.first /- z -/
      PRF.second /- w₁ -/
      PRF.third /- w again -/)
    PRF.second

--#eval eval TM.pre (Vector.fromList [2, 12])

def TM.post : PRF 2 :=
  -- post(w₁, w) = z s.t. ∃z,∃i, i.w₁.z = w
  PRF.if
    PRF.le
    (PRF.limMin
      (PRF.comp2
        PRF.eq
          (PRF.comp2 concat (PRF.comp2 concat (PRF.comp2 pre PRF.second PRF.third) PRF.second) PRF.first)
          PRF.third)
      PRF.second)
    (PRF.const 0)

-- theorem pre_post_concat_eq : ok m =
--                              evaluate g (PRF.comp2 TM.concat TM.pre (PRF.comp2 TM.concat PRF.first TM.post))
--                                       [n, m] :=
--   _

def TM.subst : PRF 3 :=
  -- subst(w₁, w₂, w) = if substring(w₁, w) then w[w₁ ← w₂] else w
  PRF.if
    (PRF.comp2 PRF.le PRF.first PRF.third)
    (PRF.comp2
      concat
      (PRF.comp2 pre PRF.first PRF.second)
      (PRF.comp2 concat PRF.second (PRF.comp2 post PRF.first PRF.third)))
    PRF.third

--#eval evaluate 100000 (TM.subst 10) [2, 1, 121]

def TM.state : PRF 1 :=
  -- get current TM state
  PRF.comp2
    pre
    (PRF.const symbolMark)
    (PRF.comp2
      post
      (PRF.const stateMark)
      PRF.first)

def TM.currentSymbol : PRF 1 :=
  PRF.comp2
    pre
    (PRF.const symbolMark)
    (PRF.comp2
      post
      (PRF.const symbolMark)
      (PRF.comp2
        post
        (PRF.const stateMark)
        PRF.first))


def TM.leftSymbol : PRF 1 :=
  PRF.comp2
    post
    (PRF.const symbolMark)
    (PRF.comp2
      pre
      (PRF.const stateMark)
      PRF.first)

def TM.nextSymbol : PRF 3 :=
  PRF.comp2
    concat
    (PRF.const symbolMark)
    (PRF.comp2
      pre
      (PRF.const movementMark)
      (PRF.comp2
        post
        (PRF.const symbolMark)
        (PRF.comp2
          post
          (PRF.comp2
            concat
            PRF.second
            PRF.third)
          PRF.first)))

def TM.nextState : PRF 3 :=
  PRF.comp2
    concat
    (PRF.const stateMark)
    (PRF.comp2
      pre
      (PRF.const symbolMark)
      (PRF.comp2
        post
        (PRF.comp2
          concat
          PRF.second
          PRF.third)
        PRF.first))

def TM.movement : PRF 3 :=
  PRF.comp2
    post
    (PRF.const movementMark)
    (PRF.comp2
      pre
      (PRF.const stepMark)
      (PRF.comp2
        post
        (PRF.comp2
          concat
          PRF.second
          PRF.third)
        PRF.first))

def TM.step : PRF 2 :=
  _

def TM.steps : PRF 3 :=
  PRF.primrec
    PRF.second
    (PRF.comp2 TM.step PRF.third PRF.first)


end TM
end PRF


open PRF.TM
def main : IO Unit :=
  IO.println s!"{PRF.eval TM.pre (Vector.fromList [2, 12])}"
