/-
The reduction `toK`, written in `TimeM`, and the proof that it outputs `enc I X K`.

Cost accounting (see the auditing rule in `Cost.lean`):
* every loop iteration is charged one `tick` (`forL`, `counterM`);
* every list append `x ++ y` is charged `x.length` steps;
* every block of O(1) clauses is emitted by `block c φ`, which charges `c` steps for the
  constant number of tests and coordinate operations that select the block, 32 steps per
  literal for computing its variable index (at most 7 pairings of 4 arithmetic
  operations each), and the encoding length of the block for writing it.
-/
import TrainNetwork.Formula

namespace TrainNetwork.Answer

open TrainNetwork TimeM

/-- Return `x`, charging `cost` steps for the work of producing it. -/
def ret {α : Type} (cost : ℕ) (x : α) : TimeM α := do
  tickN cost
  pure x

@[simp] theorem ret_val {α : Type} (cost : ℕ) (x : α) : (ret cost x).val = x := rfl
@[simp] theorem ret_time {α : Type} (cost : ℕ) (x : α) : (ret cost x).time = cost := by
  simp [ret]

/-- A for-loop over a list that concatenates the results of its body. -/
def forL {α β : Type} (l : List α) (f : α → TimeM (List β)) : TimeM (List β) :=
  match l with
  | [] => do
    tick
    pure []
  | a :: t => do
    tick
    let x ← f a
    let rest ← forL t f
    tickN x.length
    pure (x ++ rest)

@[simp] theorem forL_val {α β : Type} (l : List α) (f : α → TimeM (List β)) :
    (forL l f).val = l.flatMap fun a => (f a).val := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [forL, ih]

/-- Sequential composition that concatenates the two results. -/
def appendM {β : Type} (a b : TimeM (List β)) : TimeM (List β) := do
  let x ← a
  let y ← b
  tickN x.length
  pure (x ++ y)

@[simp] theorem appendM_val {β : Type} (a b : TimeM (List β)) :
    (appendM a b).val = a.val ++ b.val := rfl

/-- Number of literals of a list of clauses. -/
def lits (φ : List Clause) : ℕ := (φ.map List.length).sum

/-- Encoding length of a list of clauses. -/
def wsize (φ : List Clause) : ℕ := (φ.map clauseSize).sum

/-- Emit a block of O(1) clauses. -/
def block (c : ℕ) (φ : List Clause) : TimeM (List Clause) :=
  ret (c + 32 * lits φ + wsize φ) φ

@[simp] theorem block_val (c : ℕ) (φ : List Clause) : (block c φ).val = φ := rfl

/-- `[0, ..., n-1]`, one step per element. -/
def rangeM (n : ℕ) : TimeM (List ℕ) := ret (n + 1) (List.range n)

/-- All cells of the grid. -/
def cellsM (I : Instance) : TimeM (List Cell) := do
  let xs ← rangeM I.W
  let ys ← rangeM I.H
  forL xs fun x => forL ys fun y => ret 1 [(x, y)]

/-- The cells of `l` that belong to `s` (one set lookup each). -/
def filterM (l : List Cell) (s : Finset Cell) : TimeM (List Cell) :=
  forL l fun c => ret 1 (if c ∈ s then [c] else [])

def edgeM (I : Instance) (cs : List Cell) : TimeM (List Clause) :=
  forL cs fun v =>
    block 64 (edgeAt I v (v.1 + 1, v.2) ++ edgeAt I v (v.1, v.2 + 1) ++ degAt I v)

def initM (cs : List Cell) (p : Cell) : TimeM (List Clause) :=
  forL cs fun v =>
    block 1 (if v = p then [[(vGrid p 0 v, true)]]
      else [[(vGrid p 0 v, false)], [(vNet p 0 v, false)]])

def reachM (I : Instance) (cs : List Cell) (p : Cell) : TimeM (List Clause) := do
  let ts ← rangeM (I.W * I.H)
  forL ts fun t => forL cs fun v => block 128 (stepClauses I p t v)

def finM (I : Instance) (cl : List Cell) (p : Cell) : TimeM (List Clause) :=
  forL cl fun c =>
    block 4 [[(vSel p c, false), (vGrid p (I.W * I.H) c, true)],
      [(vSel p c, false), (vNet p (I.W * I.H) c, true)]]

def nearM (I : Instance) (cl : List Cell) (p : Cell) : TimeM (List Clause) := do
  let ts ← rangeM (I.W * I.H + 1)
  forL cl fun c => forL cl fun c2 => forL ts fun t =>
    block 0 [[(vSel p c, false), (vSel p c2, true), (vGrid p t c2, false), (vGrid p t c, true)]]

/-- The sequential counter of `Sat.lean`, with its loops charged. -/
def counterM (cv : ℕ → ℕ → ℕ) (B : ℕ) : ℕ → List (List Lit) → TimeM (List Clause)
  | i, [] => block 0 [[(cv i B, false)]]
  | i, it :: rest => do
    tick
    let js ← rangeM (B + 1)
    let x ← forL js fun j =>
      block 8 [[(cv i j, false), (cv (i + 1) j, true)],
        if j = 0 then negLits it ++ [(cv (i + 1) 0, true)]
        else negLits it ++ [(cv i (j - 1), false), (cv (i + 1) j, true)]]
    let r ← counterM cv B (i + 1) rest
    tickN x.length
    pure (x ++ r)

def selItemsM (cl : List Cell) (p : Cell) (b : Bool) : TimeM (List (List Lit)) :=
  forL cl fun c => ret 32 [[(vSel p c, b)]]

def cardM (I : Instance) (cl : List Cell) (p : Cell) : TimeM (List Clause) := do
  let it1 ← selItemsM cl p true
  let it0 ← selItemsM cl p false
  let n ← ret (cl.length + 2) (cl.length - I.k)
  appendM (counterM (vCount (Nat.pair 0 (cellCode p))) I.k 0 it1)
    (counterM (vCount (Nat.pair 1 (cellCode p))) n 0 it0)

def portM (I : Instance) (cs cl : List Cell) (p : Cell) : TimeM (List Clause) :=
  appendM (initM cs p) (appendM (reachM I cs p) (appendM (finM I cl p)
    (appendM (nearM I cl p) (cardM I cl p))))

def excessItemsM (I : Instance) (pl cl : List Cell) : TimeM (List (List Lit)) := do
  let ts ← rangeM (I.W * I.H)
  forL pl fun p => forL cl fun c => forL ts fun t =>
    ret 96 [[(vSel p c, true), (vGrid p t c, true), (vNet p t c, false)]]

def tileItemsM (cs : List Cell) : TimeM (List (List Lit)) :=
  forL cs fun x => ret 32 [[(vTile x, true)]]

/-- The clause list of the reduction. -/
def toKgen (I : Instance) (X K : ℕ) : TimeM (List Clause) := do
  let cs ← cellsM I
  let pl ← filterM cs I.ports
  let cl ← filterM cs I.cities
  let e ← edgeM I cs
  let ps ← forL pl (portM I cs cl)
  let xi ← excessItemsM I pl cl
  let xc ← counterM (vCount (Nat.pair 2 0)) X 0 xi
  let ti ← tileItemsM cs
  let tc ← counterM (vCount (Nat.pair 3 0)) K 0 ti
  tickN (3 * e.length + 2 * ps.length + xc.length)
  pure (e ++ ps ++ xc ++ tc)

/-- The reduction from the Train Network Problem to SAT. -/
def toK (I : Instance) (X K : ℕ) : TimeM KInstance := do
  let φ ← toKgen I X K
  pure ⟨φ⟩

/-! ### The reduction outputs `enc I X K` -/

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) :
    (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem flatMap_ite_single (l : List Cell) (s : Finset Cell) :
    (l.flatMap fun c => if c ∈ s then [c] else []) = l.filter fun c => decide (c ∈ s) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons, ih, List.filter_cons]
    split_ifs <;> simp_all

@[simp] theorem cellsM_val (I : Instance) : (cellsM I).val = cells I := by
  simp only [cellsM, rangeM, bind_val, ret_val, forL_val, flatMap_single]
  rfl

@[simp] theorem filterM_val (l : List Cell) (s : Finset Cell) :
    (filterM l s).val = l.filter fun c => decide (c ∈ s) := by
  simp only [filterM, forL_val, ret_val, flatMap_ite_single]

@[simp] theorem counterM_val (cv : ℕ → ℕ → ℕ) (B : ℕ) :
    ∀ (items : List (List Lit)) (i : ℕ), (counterM cv B i items).val = counterFrom cv B i items := by
  intro items
  induction items with
  | nil => intro i; rfl
  | cons it rest ih =>
    intro i
    simp only [counterM, counterFrom, counterStep, rangeM, bind_val, ret_val, forL_val,
      block_val, pure_val, ih]

@[simp] theorem edgeM_val (I : Instance) : (edgeM I (cells I)).val = edgeClauses I := by
  simp only [edgeM, forL_val, block_val, edgeClauses]

@[simp] theorem initM_val (I : Instance) (p : Cell) :
    (initM (cells I) p).val = initClauses I p := by
  simp only [initM, forL_val, block_val, initClauses]

@[simp] theorem reachM_val (I : Instance) (p : Cell) :
    (reachM I (cells I) p).val = reachClauses I p := by
  simp only [reachM, rangeM, bind_val, ret_val, forL_val, block_val, reachClauses]

@[simp] theorem finM_val (I : Instance) (p : Cell) :
    (finM I (cityL I) p).val = finClauses I p := by
  simp only [finM, forL_val, block_val, finClauses]

@[simp] theorem nearM_val (I : Instance) (p : Cell) :
    (nearM I (cityL I) p).val = nearClauses I p := by
  simp only [nearM, rangeM, bind_val, ret_val, forL_val, block_val, nearClauses, flatMap_single]

@[simp] theorem selItemsM_val (I : Instance) (p : Cell) (b : Bool) :
    (selItemsM (cityL I) p b).val = selItems I p b := by
  simp only [selItemsM, forL_val, ret_val, selItems, flatMap_single]

@[simp] theorem cardM_val (I : Instance) (p : Cell) :
    (cardM I (cityL I) p).val = cardClauses I p := by
  simp only [cardM, bind_val, ret_val, appendM_val, counterM_val, selItemsM_val, cardClauses,
    atMost]

@[simp] theorem portM_val (I : Instance) (p : Cell) :
    (portM I (cells I) (cityL I) p).val = portClauses I p := by
  simp only [portM, appendM_val, initM_val, reachM_val, finM_val, nearM_val, cardM_val,
    portClauses, List.append_assoc]

@[simp] theorem excessItemsM_val (I : Instance) :
    (excessItemsM I (portL I) (cityL I)).val = excessItems I := by
  simp only [excessItemsM, rangeM, bind_val, ret_val, forL_val, excessItems, flatMap_single]

@[simp] theorem tileItemsM_val (I : Instance) : (tileItemsM (cells I)).val = tileItems I := by
  simp only [tileItemsM, forL_val, ret_val, tileItems, flatMap_single]

theorem toKgen_val (I : Instance) (X K : ℕ) : (toKgen I X K).val = enc I X K := by
  have hp : (filterM (cells I) I.ports).val = portL I := by rw [filterM_val]; rfl
  have hc : (filterM (cells I) I.cities).val = cityL I := by rw [filterM_val]; rfl
  simp only [toKgen, bind_val, pure_val, cellsM_val, hp, hc, edgeM_val, forL_val, portM_val,
    excessItemsM_val, tileItemsM_val, counterM_val, enc, atMost]

theorem toK_val (I : Instance) (X K : ℕ) : (toK I X K).val = ⟨enc I X K⟩ := by
  simp only [toK, bind_val, pure_val, toKgen_val]

end TrainNetwork.Answer
