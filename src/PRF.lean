open Nat

structure Vector (n : Nat) (α : Type u) where
  val  : List α
  hasLen : List.length val = n

@[specialize] def Vector.get {α : Type u} : (as : Vector n α) → Fin n → α
  | xs, {val := i, isLt} =>
    -- List.length xs.val = n, n <= n → n <= List.length xs.val
    List.get xs.val {val := i, isLt := Nat.le_trans isLt (Eq.subst (Eq.symm xs.hasLen) Nat.le.refl)}

@[specialize] def Vector.fromList {α : Type u} : (as : List α) → Vector (List.length as) α
  | xs => {val := xs, hasLen := rfl}

@[specialize] def Vector.enumeration {α : Type u} : Vector n α → (Fin n → α)
  | as => λ i => Vector.get as i

namespace PRF
inductive PRF : Nat → Type where
  | zero    : PRF 0
  | succ    : PRF 1
  | proj    : {n : Nat} → Fin n → PRF n -- projection
  -- composition: f(x) = g(h₁(x*),...,hₘ(x*)), where arity(f) = k, arity(g) = m, arity(hᵢ) = k
  | comp    : {m k : Nat} → PRF m → (Fin m → PRF k) → PRF k
  -- primitive recursion: f(0, x*) = g(x*); f(n + 1, x*) = h(f(n, x*), n, x*)
  | primrec : {n : Nat} → PRF n → PRF (n + 2) → PRF (n + 1) -- primitive recursion

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

--#eval eval PRF.add (Vector.fromList [3, 2])

def PRF.mul : PRF 2 :=
  PRF.primrec
    (PRF.const 0)
    (PRF.comp2 PRF.add (PRF.proj 0) (PRF.proj 2))

--#eval eval PRF.mul (Vector.fromList [3, 0])
--#eval eval PRF.mul (Vector.fromList [3, 4])

def PRF.exp : PRF 2 :=
  PRF.comp2
    (PRF.primrec
      (PRF.const 1)
      (PRF.comp2 PRF.mul PRF.first (PRF.proj 2)))
    PRF.second
    PRF.first

-- #eval eval PRF.exp (Vector.fromList [0, 0])
-- #eval eval PRF.exp (Vector.fromList [0, 1])
-- #eval eval PRF.exp (Vector.fromList [10, 0])
--#eval eval PRF.exp (Vector.fromList [10, 2])

def PRF.pred : PRF 1 :=
  PRF.primrec (PRF.const 0) PRF.second

-- #eval eval PRF.pred (Vector.fromList [2])

def PRF.signal : PRF 1 :=
  PRF.primrec
    (PRF.const 0)
    (PRF.const 1)

--#eval eval PRF.signal (Vector.fromList [0])
--#eval eval PRF.signal (Vector.fromList [1])
-- #eval eval PRF.signal (Vector.fromList [20])

def PRF.le : PRF 2 :=
  PRF.comp1 PRF.signal
    (PRF.primrec
      (PRF.comp1 PRF.succ PRF.first)
      (PRF.comp1 PRF.pred PRF.first))

-- #eval eval PRF.le (Vector.fromList [9, 10])
-- #eval eval PRF.le (Vector.fromList [10, 10])
-- #eval eval PRF.le (Vector.fromList [2, 1])

def PRF.lt : PRF 2 :=
  PRF.comp2 PRF.le (PRF.comp1 PRF.succ PRF.first) PRF.second

--#eval eval PRF.lt (Vector.fromList [9, 10])
--#eval eval PRF.lt (Vector.fromList [10, 10])
--#eval eval PRF.lt (Vector.fromList [2, 1])

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

--#eval eval (PRF.if PRF.first PRF.first PRF.not) (Vector.fromList [0])

def PRF.or : PRF 2 :=
  PRF.comp1 PRF.signal (PRF.comp2 PRF.add PRF.first PRF.second)

def PRF.and : PRF 2 :=
  PRF.comp2 PRF.mul (PRF.comp1 PRF.signal PRF.first) (PRF.comp1 PRF.signal PRF.second)

-- #eval eval PRF.and (Vector.fromList [2, 0])

def PRF.eq : PRF 2 :=
  PRF.comp2
    PRF.and
    PRF.le
    (PRF.comp2 PRF.le PRF.second PRF.first)

--#eval eval PRF.eq (Vector.fromList [0, 1])
--#eval eval PRF.eq (Vector.fromList [11, 11])
--#eval eval PRF.eq (Vector.fromList [2, 1])

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

--#eval eval (PRF.dropNth 0 PRF.le) (Vector.fromList [4, 5 , 3])

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

--#eval eval (@PRF.firstLEsat 0 (PRF.comp2 PRF.le (PRF.const 5) PRF.first) (PRF.const 10)) (Vector.fromList [1])

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

--#eval eval (@PRF.disjunction 0 (PRF.comp2 PRF.le (PRF.const 13) PRF.first)) (Vector.fromList [0])

def PRF.limMin : PRF (k + 1) → PRF k → PRF k
  -- (μ z ≤ g(x₁, ..., xₙ))[h(z, x₁, ..., xₙ) > 0]
  | h, g => PRF.firstLEsat h g

-- #eval eval
--         (PRF.limMin
--           (PRF.comp2 PRF.le (PRF.const 3) PRF.first)
--           (@PRF.comp2 1 PRF.add PRF.first (PRF.const 1)))
--         (Vector.fromList [2])

namespace TM

inductive Move where
  | left : Move
  | right : Move
  | stop : Move

structure Transition where
  sttState : Nat
  sttSymbol : Nat
  endState : Nat
  endSymbol : Nat
  move : Move

structure TuringMachine where
  rules  : List Transition
  finalState : Nat

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

def TM.encode : TuringMachine → Nat
  -- encoding as {finalState}{transitions}
  --- state is Q{bitstring}, symbol is S{bitstring}
  -- transition is {begin state}{begin symbol}{end state}{end
  --- symbol}{movement separator}{movement}{rule separator}
  -- current state goes in the tape instead
  | tm =>
    String.toNat! <|
      String.join
        [ encodeState tm.finalState
        , String.intercalate
            (toString stepMark)
            (List.map encodeStep tm.rules)
        ]
  where
    encodeState : Nat → String
    | st => toString stateMark ++ toString st
    encodeSymbol : Nat → String
    | sy => toString symbolMark ++ toString sy
    encodeMove : Move → String
    | m => toString
        <| match m with
           | Move.left => leftMark
           | Move.right => rightMark
           | Move.stop => stopMark
    encodeStep : Transition → String
    | tr =>
      String.join
        [ encodeState tr.sttState
        , encodeSymbol tr.sttSymbol
        , encodeState tr.endState
        , encodeSymbol tr.endSymbol
        , toString movementMark
        , encodeMove tr.move
        ]

def TM.unarySucc : TuringMachine :=
  { rules :=
    [ { sttState := 0
      , sttSymbol := 1
      , endState := 0
      , endSymbol := 1
      , move := Move.right
      }
    , { sttState := 0
      , sttSymbol := emptyMark
      , endState := 1
      , endSymbol := 1
      , move := Move.stop
      }
    ]
  , finalState := 1
  }

--#eval TM.encode TM.unarySucc

def TM.binarySucc : TuringMachine :=
  { rules :=
    [ { sttState := 0
      , sttSymbol := 1
      , endState := 0
      , endSymbol := 1
      , move := Move.right
      }
    , { sttState := 0
      , sttSymbol := emptyMark
      , endState := 1
      , endSymbol := emptyMark
      , move := Move.left
      }
    , { sttState := 1
      , sttSymbol := 1
      , endState := 1
      , endSymbol := 1
      , move := Move.left
      }
    , { sttState := 0
      , sttSymbol := 0
      , endState := 0
      , endSymbol := 0
      , move := Move.right
      }
    , { sttState := 1
      , sttSymbol := 0
      , endState := 10
      , endSymbol := 1
      , move := Move.stop
      }
    , { sttState := 1
      , sttSymbol := emptyMark
      , endState := 10
      , endSymbol := 1
      , move := Move.stop
      }
    ]
  , finalState := 10
  }

def TM.len : PRF 1 :=
  -- lenₖ(w) = z such that k^z > w and ∀n, k^n > w → n > z
  PRF.limMin
    (PRF.comp2 PRF.lt PRF.second (PRF.comp2 PRF.exp (PRF.const k) PRF.first))
    PRF.identity

--#eval eval TM.len (Vector.fromList [10])

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

--#eval eval (TM.concat 10) (Vector.fromList [1, 1])

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

-- theorem pre_post_concat_eq : m =
--                              eval (PRF.comp2 TM.concat TM.pre (PRF.comp2 TM.concat PRF.first TM.post))
--                                       [n, m] :=
--   _

def TM.substring : PRF 2 :=
  PRF.comp2
    (PRF.disjunction
      (PRF.comp2
        PRF.eq
        PRF.second
        (PRF.comp2
          TM.concat
          (PRF.comp2 TM.pre PRF.first PRF.second)
          (PRF.comp2
            TM.concat
            PRF.first
            (PRF.comp2
              TM.post
              PRF.first
              PRF.second)))))
    PRF.second
    PRF.first

--#eval eval TM.pre (Vector.fromList [2, 11])

def TM.subst : PRF 3 :=
  -- subst(w₁, w₂, w) = if substring(w₁, w) then w[w₁ ← w₂] else w
  PRF.if
    (PRF.comp2 TM.substring PRF.first PRF.third)
    (PRF.comp2
      concat
      (PRF.comp2 pre PRF.first PRF.second)
      (PRF.comp2 concat PRF.second (PRF.comp2 post PRF.first PRF.third)))
    PRF.third

--#eval eval (TM.subst 10) (Vector.fromList [2, 1, 121])

def TM.state : PRF 1 :=
  -- get current TM state
  PRF.comp2
    TM.concat
    (PRF.const stateMark)
    (PRF.comp2
      pre
      (PRF.const symbolMark)
      (PRF.comp2
        post
        (PRF.const stateMark)
        PRF.first))

def TM.currentSymbol : PRF 1 :=
  PRF.comp2
    TM.concat
    (PRF.const symbolMark)
    (PRF.comp2
      pre
      (PRF.const symbolMark)
      (PRF.comp2
        post
        (PRF.const symbolMark)
        (PRF.comp2
          post
          (PRF.const stateMark)
          PRF.first)))


def TM.leftSymbol : PRF 1 :=
  PRF.comp2
    TM.concat
    (PRF.const symbolMark)
    (PRF.comp2
      post
      (PRF.const symbolMark)
      (PRF.comp2
        pre
        (PRF.const stateMark)
        PRF.first))

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
  let machine := PRF.first
  let tape := PRF.second
  let currState := PRF.comp1 TM.state PRF.second
  let currSymbol := PRF.comp1 TM.currentSymbol PRF.second
  let currentMove :=
    PRF.comp3
      TM.movement
      PRF.first
      currState
      currSymbol
  let equals := λ a1 a2 => PRF.comp2 PRF.eq a1 a2
  let concat := λ a1 a2 => PRF.comp2 TM.concat a1 a2
  let subst := λ a1 a2 a3 => PRF.comp3 TM.subst a1 a2 a3
  let nextState := PRF.comp3 TM.nextState machine currState currSymbol
  let nextSymbol := PRF.comp3 TM.nextSymbol machine currState currSymbol
  let leftSymbol := PRF.comp1 TM.leftSymbol tape
  PRF.if
    (equals currentMove (PRF.const rightMark))
    -- next move is to the right
    (subst
      (concat currState currSymbol)
      (concat nextSymbol nextState)
      tape)
    (PRF.if
      (equals currentMove (PRF.const leftMark))
      -- next move is to the left (to the left, to the left)
      (subst
        (concat leftSymbol (concat currState currSymbol))
        (concat nextState (concat leftSymbol nextSymbol))
        tape)
      -- we stop here
      (subst
        (concat currState currSymbol)
        (concat nextState nextSymbol)
        tape))

def TM.steps : PRF 3 :=
  PRF.primrec
    PRF.second
    (PRF.comp2 TM.step PRF.third PRF.first)


end TM
end PRF


open PRF.TM
def main : IO Unit :=
  IO.println s!"{PRF.eval TM.pre (Vector.fromList [2, 12])}"
