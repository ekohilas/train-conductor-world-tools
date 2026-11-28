/-
`TimeM` implementations of the functions of `Exec.lean` and `Search.lean`.

Cost accounting (see the auditing rule in `Cost.lean`):

* Every list combinator below (`filterT`, `mapT`, `allT`, `foldlT`, `flatMapT`, `memT`,
  `dedupT`, `lengthT`, `appendT`, `sumT`, `rangeT`) is a structural recursion that
  charges at least one `tick` per element visited, in addition to the cost of the
  function it applies.
* Comparing two cells is charged 2 ticks (two comparisons of natural numbers).
* A membership test in one of the instance's finsets (`blocked`, `ports`, `cities`) is
  charged `I.size` ticks. These sets lie inside the grid, so they have fewer than
  `I.size` elements, and a linear scan costs at most that many cell comparisons.
* Every other pure expression between ticks is O(1) work on a bounded number of
  natural numbers, Booleans or constructors, and is preceded by a `tick`/`tickN`.

For every timed function `fT` there is a lemma `fT_val` stating that its value is the
pure function `f` of `Exec.lean`/`Search.lean`. Running times are bounded in
`TimeBound.lean`.
-/
import TrainNetwork.Search

namespace TrainNetwork

namespace TimeM

@[simp] theorem tick_val : tick.val = () := rfl
@[simp] theorem tickN_val (n : ℕ) : (tickN n).val = () := rfl

end TimeM

open TimeM

/-! ### List combinators -/

section Combinators

variable {α β : Type}

/-- `List.filter` with a timed predicate; one extra tick per element. -/
def filterT (p : α → TimeM Bool) : List α → TimeM (List α)
  | [] => pure []
  | a :: l => do
    tick
    let b ← p a
    let r ← filterT p l
    pure (if b then a :: r else r)

@[simp] theorem filterT_val (p : α → TimeM Bool) :
    ∀ l : List α, (filterT p l).val = l.filter (fun a => (p a).val)
  | [] => rfl
  | a :: l => by
    simp only [filterT, bind_val, pure_val, filterT_val p l, List.filter_cons]

/-- `List.map` with a timed function; one extra tick per element. -/
def mapT (f : α → TimeM β) : List α → TimeM (List β)
  | [] => pure []
  | a :: l => do
    tick
    let b ← f a
    let r ← mapT f l
    pure (b :: r)

@[simp] theorem mapT_val (f : α → TimeM β) :
    ∀ l : List α, (mapT f l).val = l.map (fun a => (f a).val)
  | [] => rfl
  | a :: l => by simp only [mapT, bind_val, pure_val, mapT_val f l, List.map_cons]

/-- `List.all` with a timed predicate (no short-circuit); one extra tick per element. -/
def allT (p : α → TimeM Bool) : List α → TimeM Bool
  | [] => pure true
  | a :: l => do
    tick
    let b ← p a
    let r ← allT p l
    pure (b && r)

@[simp] theorem allT_val (p : α → TimeM Bool) :
    ∀ l : List α, (allT p l).val = l.all (fun a => (p a).val)
  | [] => rfl
  | a :: l => by simp only [allT, bind_val, pure_val, allT_val p l, List.all_cons]

/-- `List.foldl` with a timed step; one extra tick per element. -/
def foldlT (f : β → α → TimeM β) : β → List α → TimeM β
  | b, [] => pure b
  | b, a :: l => do
    tick
    let b' ← f b a
    foldlT f b' l

@[simp] theorem foldlT_val (f : β → α → TimeM β) :
    ∀ (l : List α) (b : β), (foldlT f b l).val = l.foldl (fun b a => (f b a).val) b
  | [], b => rfl
  | a :: l, b => by simp only [foldlT, bind_val, foldlT_val f l, List.foldl_cons]

/-- `l₁ ++ l₂`; one tick per element of `l₁`. -/
def appendT : List α → List α → TimeM (List α)
  | [], l₂ => pure l₂
  | a :: l₁, l₂ => do
    tick
    let r ← appendT l₁ l₂
    pure (a :: r)

@[simp] theorem appendT_val : ∀ l₁ l₂ : List α, (appendT l₁ l₂).val = l₁ ++ l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => by simp only [appendT, bind_val, pure_val, appendT_val l₁ l₂, List.cons_append]

/-- `List.flatMap` with a timed function; one extra tick per element, plus the appends. -/
def flatMapT (f : α → TimeM (List β)) : List α → TimeM (List β)
  | [] => pure []
  | a :: l => do
    tick
    let x ← f a
    let r ← flatMapT f l
    appendT x r

@[simp] theorem flatMapT_val (f : α → TimeM (List β)) :
    ∀ l : List α, (flatMapT f l).val = l.flatMap (fun a => (f a).val)
  | [] => rfl
  | a :: l => by
    simp only [flatMapT, bind_val, appendT_val, flatMapT_val f l, List.flatMap_cons]

/-- `List.length`; one tick per element. -/
def lengthT : List α → TimeM ℕ
  | [] => pure 0
  | _ :: l => do
    tick
    let n ← lengthT l
    pure (n + 1)

@[simp] theorem lengthT_val : ∀ l : List α, (lengthT l).val = l.length
  | [] => rfl
  | a :: l => by simp only [lengthT, bind_val, pure_val, lengthT_val l, List.length_cons]

/-- Sum of a list of naturals; one tick per element. -/
def sumT : List ℕ → TimeM ℕ
  | [] => pure 0
  | a :: l => do
    tick
    let n ← sumT l
    pure (a + n)

@[simp] theorem sumT_val : ∀ l : List ℕ, (sumT l).val = l.sum
  | [] => rfl
  | a :: l => by simp only [sumT, bind_val, pure_val, sumT_val l, List.sum_cons]

/-- Membership test by linear scan (no short-circuit); `c` ticks per element, where `c`
is the cost of comparing two elements. -/
def memT [DecidableEq α] (c : ℕ) (a : α) : List α → TimeM Bool
  | [] => pure false
  | b :: l => do
    tickN c
    let r ← memT c a l
    pure (decide (a = b) || r)

@[simp] theorem memT_val [DecidableEq α] (c : ℕ) (a : α) :
    ∀ l : List α, (memT c a l).val = decide (a ∈ l)
  | [] => by simp [memT]
  | b :: l => by
    simp only [memT, bind_val, pure_val, memT_val c a l, List.mem_cons, Bool.decide_or]

/-- `List.dedup`; one tick plus one membership scan per element. -/
def dedupT [DecidableEq α] (c : ℕ) : List α → TimeM (List α)
  | [] => pure []
  | a :: l => do
    tick
    let b ← memT c a l
    let r ← dedupT c l
    pure (if b then r else a :: r)

@[simp] theorem dedupT_val [DecidableEq α] (c : ℕ) :
    ∀ l : List α, (dedupT c l).val = l.dedup
  | [] => rfl
  | a :: l => by
    simp only [dedupT, bind_val, pure_val, memT_val, dedupT_val c l]
    by_cases h : a ∈ l
    · simp [h, List.dedup_cons_of_mem h]
    · simp [h, List.dedup_cons_of_notMem h]

/-- `List.range`. -/
def rangeT : ℕ → TimeM (List ℕ)
  | 0 => pure []
  | n + 1 => do
    tick
    let r ← rangeT n
    appendT r [n]

@[simp] theorem rangeT_val : ∀ n : ℕ, (rangeT n).val = List.range n
  | 0 => rfl
  | n + 1 => by simp only [rangeT, bind_val, appendT_val, rangeT_val n, List.range_succ]

end Combinators

/-! ### The grid -/

namespace Instance

variable (I : Instance)

/-- `c ∈ I.blocked`, charged `I.size` ticks (a linear scan over fewer than `I.size`
cells). -/
def memBlockedT (c : Cell) : TimeM Bool := do
  tickN I.size
  pure (decide (c ∈ I.blocked))

def memPortsT (c : Cell) : TimeM Bool := do
  tickN I.size
  pure (decide (c ∈ I.ports))

def memCitiesT (c : Cell) : TimeM Bool := do
  tickN I.size
  pure (decide (c ∈ I.cities))

def isOpenT (c : Cell) : TimeM Bool := do
  tickN 2
  let b ← I.memBlockedT c
  pure (decide (c.1 < I.W) && decide (c.2 < I.H) && !b)

@[simp] theorem isOpenT_val (c : Cell) : (I.isOpenT c).val = I.isOpenB c := rfl

def isFreeT (c : Cell) : TimeM Bool := do
  let o ← I.isOpenT c
  let p ← I.memPortsT c
  let q ← I.memCitiesT c
  tick
  pure (o && !p && !q)

@[simp] theorem isFreeT_val (c : Cell) : (I.isFreeT c).val = I.isFreeB c := rfl

/-- Adjacency test: a bounded number of arithmetic operations and comparisons on four
natural numbers (charged 16), plus two openness tests. -/
def gridAdjT (a b : Cell) : TimeM Bool := do
  tickN 16
  let oa ← I.isOpenT a
  let ob ← I.isOpenT b
  pure (decide (Adjacent a b) && oa && ob)

@[simp] theorem gridAdjT_val (a b : Cell) : (I.gridAdjT a b).val = I.gridAdjB a b := rfl

def cellsT : TimeM (List Cell) := do
  let xs ← rangeT I.W
  let ys ← rangeT I.H
  flatMapT (fun x => mapT (fun y => do tick; pure (x, y)) ys) xs

@[simp] theorem cellsT_val : I.cellsT.val = I.cellsL := by
  simp [cellsT, cellsL]

/-- The four potential neighbours: four arithmetic operations (charged 8). -/
def nbr4T (a : Cell) : TimeM (List Cell) := do
  tickN 8
  pure (nbr4 a)

def gridEdgesT (cells : List Cell) : TimeM (List (Cell × Cell)) :=
  flatMapT (fun a => do
    let nb ← nbr4T a
    let ok ← filterT (fun b => I.gridAdjT a b) nb
    mapT (fun b => do tick; pure (a, b)) ok) cells

@[simp] theorem gridEdgesT_val : (I.gridEdgesT I.cellsL).val = I.gridEdgesL := by
  simp [gridEdgesT, gridEdgesL, nbr4T]

def portsT (cells : List Cell) : TimeM (List Cell) := filterT I.memPortsT cells

@[simp] theorem portsT_val : (I.portsT I.cellsL).val = I.portsL := by
  simp [portsT, portsL, memPortsT]

def citiesT (cells : List Cell) : TimeM (List Cell) := filterT I.memCitiesT cells

@[simp] theorem citiesT_val : (I.citiesT I.cellsL).val = I.citiesL := by
  simp [citiesT, citiesL, memCitiesT]

end Instance

/-! ### Distances -/

/-- Timed `stepL`. -/
def stepT (I : Instance) (E : List (Cell × Cell)) (first : Bool) (A : List Cell) :
    TimeM (List Cell) := do
  let l₁ ← filterT (fun e => do
    let m ← memT 2 e.1 A
    let f ← I.isFreeT e.1
    tick
    pure (m && (first || f))) E
  let r₁ ← mapT (fun e => do tick; pure e.2) l₁
  let l₂ ← filterT (fun e => do
    let m ← memT 2 e.2 A
    let f ← I.isFreeT e.2
    tick
    pure (m && (first || f))) E
  let r₂ ← mapT (fun e => do tick; pure e.1) l₂
  appendT r₁ r₂

@[simp] theorem stepT_val (I : Instance) (E : List (Cell × Cell)) (first : Bool)
    (A : List Cell) : (stepT I E first A).val = stepL I.isFreeB E first A := by
  simp [stepT, stepL]

/-- Timed `distL`. -/
def distT (I : Instance) (E : List (Cell × Cell)) (t : Cell) :
    ℕ → ℕ → List Cell → TimeM (Option ℕ)
  | 0, i, A => do
    tick
    let m ← memT 2 t A
    pure (if m then some i else none)
  | f + 1, i, A => do
    tick
    let m ← memT 2 t A
    if m then pure (some i) else do
      let A' ← stepT I E (i == 0) A
      distT I E t f (i + 1) A'

@[simp] theorem distT_val (I : Instance) (E : List (Cell × Cell)) (t : Cell) :
    ∀ (f i : ℕ) (A : List Cell), (distT I E t f i A).val = distL I.isFreeB E t f i A
  | 0, i, A => by
    simp only [distT, distL, bind_val, pure_val, memT_val]
    by_cases h : t ∈ A <;> simp [h]
  | f + 1, i, A => by
    simp only [distT, distL, bind_val, memT_val]
    by_cases h : t ∈ A
    · simp [h]
    · simp [h, distT_val I E t f]

/-- Timed `netDistO`. -/
def netDistT (I : Instance) (E : List (Cell × Cell)) (s t : Cell) : TimeM (Option ℕ) := do
  let n ← lengthT E
  tick
  distT I E t (2 * n) 0 [s]

@[simp] theorem netDistT_val (I : Instance) (E : List (Cell × Cell)) (s t : Cell) :
    (netDistT I E s t).val = netDistO I.isFreeB E s t := by
  simp [netDistT, netDistO]

/-! ### The feasibility test and the cost -/

/-- Timed `lookupL`; one cell comparison per entry. -/
def lookupT (p : Cell) : List (Cell × List Cell) → TimeM (List Cell)
  | [] => pure []
  | (q, S) :: r => do
    tickN 2
    if q = p then pure S else lookupT p r

@[simp] theorem lookupT_val (p : Cell) :
    ∀ ch : List (Cell × List Cell), (lookupT p ch).val = lookupL p ch
  | [] => rfl
  | (q, S) :: r => by
    simp only [lookupT, lookupL, bind_val]
    by_cases h : q = p
    · simp [h]
    · simp [h, lookupT_val p r]

def endsT (E : List (Cell × Cell)) : TimeM (List Cell) := do
  let a ← mapT (fun e => do tick; pure e.1) E
  let b ← mapT (fun e => do tick; pure e.2) E
  appendT a b

@[simp] theorem endsT_val (E : List (Cell × Cell)) : (endsT E).val = endsL E := by
  simp [endsT, endsL]

def nbrT (E : List (Cell × Cell)) (x : Cell) : TimeM (List Cell) := do
  let l₁ ← filterT (fun e => do tickN 2; pure (decide (e.1 = x))) E
  let r₁ ← mapT (fun e => do tick; pure e.2) l₁
  let l₂ ← filterT (fun e => do tickN 2; pure (decide (e.2 = x))) E
  let r₂ ← mapT (fun e => do tick; pure e.1) l₂
  appendT r₁ r₂

@[simp] theorem nbrT_val (E : List (Cell × Cell)) (x : Cell) : (nbrT E x).val = nbrL E x := by
  simp [nbrT, nbrL]

def degOKT (I : Instance) (E : List (Cell × Cell)) : TimeM Bool := do
  let ends ← endsT E
  allT (fun x => do
    let f ← I.isFreeT x
    let nb ← nbrT E x
    let d ← dedupT 2 nb
    let n ← lengthT d
    tick
    pure (!f || decide (n ≤ 3))) ends

@[simp] theorem degOKT_val (I : Instance) (E : List (Cell × Cell)) :
    (degOKT I E).val = degOK I E := by
  simp [degOKT, degOK]

def tilesT (I : Instance) (E : List (Cell × Cell)) : TimeM ℕ := do
  let ends ← endsT E
  let fr ← filterT I.isFreeT ends
  let d ← dedupT 2 fr
  lengthT d

@[simp] theorem tilesT_val (I : Instance) (E : List (Cell × Cell)) :
    (tilesT I E).val = tilesN I E := by
  simp only [tilesT, tilesN, bind_val, endsT_val, filterT_val, dedupT_val, lengthT_val,
    Instance.isFreeT_val]

/-- Timed `selOK`. `ge` is the list of grid edges, `cities` the list of cities, and `S`
the list chosen for port `p`. -/
def selOKT (I : Instance) (ge : List (Cell × Cell)) (cities S : List Cell) (p : Cell) :
    TimeM Bool := do
  let a ← allT I.memCitiesT S
  let d ← dedupT 2 S
  let n ← lengthT d
  tick
  let b ← allT (fun x => do
    let g ← netDistT I ge p x
    tick
    pure g.isSome) S
  let c ← allT (fun x => allT (fun y => do
    let m ← memT 2 y S
    let gx ← netDistT I ge p x
    let gy ← netDistT I ge p y
    tickN 2
    pure (m || leO gx gy)) cities) S
  pure (a && decide (n = I.k) && b && c)

@[simp] theorem selOKT_val (I : Instance) (c : Cand) (p : Cell) :
    (selOKT I I.gridEdgesL I.citiesL (c.sel p) p).val = selOK I c p := by
  simp [selOKT, selOK, Instance.gridDistO, Instance.memCitiesT]

def connOKT (I : Instance) (E : List (Cell × Cell)) (S : List Cell) (p : Cell) :
    TimeM Bool :=
  allT (fun x => do
    let g ← netDistT I E p x
    tick
    pure g.isSome) S

@[simp] theorem connOKT_val (I : Instance) (c : Cand) (p : Cell) :
    (connOKT I c.edges (c.sel p) p).val = connOK I c p := by
  simp [connOKT, connOK]

def feasT (I : Instance) (ge : List (Cell × Cell)) (ports cities : List Cell) (c : Cand) :
    TimeM Bool := do
  let a ← allT (fun e => I.gridAdjT e.1 e.2) c.edges
  let b ← degOKT I c.edges
  let d ← allT (fun p => do
    let S ← lookupT p c.choice
    let s₁ ← selOKT I ge cities S p
    let s₂ ← connOKT I c.edges S p
    tick
    pure (s₁ && s₂)) ports
  pure (a && b && d)

@[simp] theorem feasT_val (I : Instance) (c : Cand) :
    (feasT I I.gridEdgesL I.portsL I.citiesL c).val = feasB I c := by
  simp only [feasT, feasB, bind_val, pure_val, allT_val, Instance.gridAdjT_val, degOKT_val,
    lookupT_val]
  have h : ∀ p, (selOKT I I.gridEdgesL I.citiesL (lookupL p c.choice) p).val = selOK I c p :=
    fun p => selOKT_val I c p
  have h' : ∀ p, (connOKT I c.edges (lookupL p c.choice) p).val = connOK I c p :=
    fun p => connOKT_val I c p
  simp only [h, h']

def excessT (I : Instance) (ge : List (Cell × Cell)) (ports : List Cell) (c : Cand) :
    TimeM ℕ := do
  let xs ← mapT (fun p => do
    let S ← lookupT p c.choice
    let d ← dedupT 2 S
    let ys ← mapT (fun x => do
      let a ← netDistT I c.edges p x
      let b ← netDistT I ge p x
      tickN 3
      pure (a.getD 0 - b.getD 0)) d
    sumT ys) ports
  sumT xs

@[simp] theorem excessT_val (I : Instance) (c : Cand) :
    (excessT I I.gridEdgesL I.portsL c).val = excessN I c := by
  simp [excessT, excessN, pairEx, Cand.sel, Instance.gridDistO]

def costT (I : Instance) (ge : List (Cell × Cell)) (ports : List Cell) (c : Cand) :
    TimeM (ℕ × ℕ) := do
  let x ← excessT I ge ports c
  let t ← tilesT I c.edges
  tick
  pure (x, t)

@[simp] theorem costT_val (I : Instance) (c : Cand) :
    (costT I I.gridEdgesL I.portsL c).val = costN I c := by
  simp [costT, costN]

/-- Timed `better`. The comparison of two costs is charged 3 ticks. -/
def betterT (I : Instance) (ge : List (Cell × Cell)) (ports cities : List Cell)
    (acc : Option (Cand × (ℕ × ℕ))) (c : Cand) : TimeM (Option (Cand × (ℕ × ℕ))) := do
  let f ← feasT I ge ports cities c
  if f then do
    let k ← costT I ge ports c
    tickN 3
    match acc with
    | none => pure (some (c, k))
    | some (b, cb) => pure (if lexLe cb k then some (b, cb) else some (c, k))
  else pure acc

@[simp] theorem betterT_val (I : Instance) (acc : Option (Cand × (ℕ × ℕ))) (c : Cand) :
    (betterT I I.gridEdgesL I.portsL I.citiesL acc c).val = better I acc c := by
  simp only [betterT, better, bind_val, feasT_val]
  by_cases h : feasB I c = true
  · simp only [h, ↓reduceIte, bind_val, costT_val]
    cases acc with
    | none => rfl
    | some r => rfl
  · have h' : feasB I c = false := by simpa using h
    simp [h']

/-! ### Enumeration -/

/-- Timed `subl`. -/
def sublT {α : Type} : List α → TimeM (List (List α))
  | [] => do
    tick
    pure [[]]
  | a :: l => do
    tick
    let r ← sublT l
    let r' ← mapT (fun s => do tick; pure (a :: s)) r
    appendT r r'

@[simp] theorem sublT_val {α : Type} : ∀ l : List α, (sublT l).val = subl l
  | [] => rfl
  | a :: l => by simp [sublT, subl, sublT_val l]

/-- Timed `choicesL`. -/
def choicesT (sub : List (List Cell)) : List Cell → TimeM (List (List (Cell × List Cell)))
  | [] => do
    tick
    pure [[]]
  | p :: ps => do
    tick
    let r ← choicesT sub ps
    flatMapT (fun S => mapT (fun x => do tick; pure ((p, S) :: x)) r) sub

@[simp] theorem choicesT_val (sub : List (List Cell)) :
    ∀ ps : List Cell, (choicesT sub ps).val = choicesL sub ps
  | [] => rfl
  | p :: ps => by simp [choicesT, choicesL, choicesT_val sub ps]

/-! ### The solver -/

/-- The exhaustive solver in `TimeM`: enumerate every edge subset of the grid and every
choice of city lists, test feasibility, and keep the cheapest. The final conversion of
the winning edge list to a `Finset` is charged quadratically in its length. -/
def solveT (I : Instance) : TimeM (Option Solution) := do
  let cells ← I.cellsT
  let ge ← I.gridEdgesT cells
  let ports ← I.portsT cells
  let cities ← I.citiesT cells
  let es ← sublT ge
  let cs ← sublT cities
  let chs ← choicesT cs ports
  let r ← foldlT (fun acc E =>
    foldlT (fun acc ch => betterT I ge ports cities acc ⟨E, ch⟩) acc chs) none es
  match r with
  | none => do
    tick
    pure none
  | some (c, _) => do
    tickN (c.edges.length * c.edges.length + 1)
    pure (some c.toSolution)

theorem solveT_val (I : Instance) : (solveT I).val = solvePure I := by
  simp only [solveT, bind_val, Instance.cellsT_val, Instance.gridEdgesT_val,
    Instance.portsT_val, Instance.citiesT_val, sublT_val, choicesT_val, foldlT_val,
    betterT_val]
  have hfold : (subl I.gridEdgesL).foldl (fun acc E =>
      (choicesL (subl I.citiesL) I.portsL).foldl
        (fun acc ch => better I acc ⟨E, ch⟩) acc) none = best I (allCands I) := by
    simp only [best, allCands, List.foldl_flatMap, List.foldl_map]
  rw [hfold]
  unfold solvePure solveFrom
  cases best I (allCands I) with
  | none => rfl
  | some r => rfl

end TrainNetwork
