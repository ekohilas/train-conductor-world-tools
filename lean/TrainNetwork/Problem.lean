/-
Frozen formal definition of the Train Network Problem.

This file mirrors `docs/problem.md` exactly. Do NOT edit it to make a proof easier:
any change to the problem must be made to `docs/problem.md`, this file and
`network_solver/verify.py` together, and is out of scope for a proof attempt.
-/
import Mathlib

open Classical

namespace TrainNetwork

/-- A grid cell `(x, y)`. -/
abbrev Cell := ℕ × ℕ

/-- 4-neighbour adjacency. -/
def Adjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
  (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1))

/-- A problem instance (docs/problem.md, "Input"). Ports and cities are identified by
their cells, which are distinct. -/
structure Instance where
  W : ℕ
  H : ℕ
  blocked : Finset Cell
  ports : Finset Cell
  cities : Finset Cell
  k : ℕ
  k_pos : 0 < k
  k_le_cities : k ≤ cities.card
  ports_cities : Disjoint ports cities
  ports_unblocked : Disjoint ports blocked
  cities_unblocked : Disjoint cities blocked
  ports_inBounds : ∀ p ∈ ports, p.1 < W ∧ p.2 < H
  cities_inBounds : ∀ c ∈ cities, c.1 < W ∧ c.2 < H
  blocked_inBounds : ∀ b ∈ blocked, b.1 < W ∧ b.2 < H

namespace Instance

variable (I : Instance)

def InBounds (c : Cell) : Prop := c.1 < I.W ∧ c.2 < I.H

def IsTerminal (c : Cell) : Prop := c ∈ I.ports ∨ c ∈ I.cities

/-- A free cell may hold a track tile. -/
def IsFree (c : Cell) : Prop := I.InBounds c ∧ c ∉ I.blocked ∧ ¬ I.IsTerminal c

/-- Cells a track edge may touch. -/
def IsOpen (c : Cell) : Prop := I.InBounds c ∧ c ∉ I.blocked

/-- Grid adjacency restricted to open cells. -/
def GridAdj (a b : Cell) : Prop := Adjacent a b ∧ I.IsOpen a ∧ I.IsOpen b

/-- `w` is a walk from `s` to `t` along relation `R`, whose intermediate cells are all
free (paths never pass through blocked cells or other terminals). Its length is
`w.length - 1`. -/
def IsWalk (R : Cell → Cell → Prop) (s t : Cell) (w : List Cell) : Prop :=
  w.head? = some s ∧ w.getLast? = some t ∧ w.IsChain R ∧
  ∀ x ∈ (w.dropLast).tail, I.IsFree x

/-- Shortest walk length along `R`, or `⊤` if none exists. -/
noncomputable def walkDist (R : Cell → Cell → Prop) (s t : Cell) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ w, I.IsWalk R s t w ∧ n = ((w.length - 1 : ℕ) : ℕ∞)}

/-- `d(p, c)` from docs/problem.md, "Grid distance". -/
noncomputable def gridDist (s t : Cell) : ℕ∞ := I.walkDist I.GridAdj s t

/-- A valid choice of cities for port `p`: `k` cities, all reachable, and none of them
farther than any unchosen city. This is exactly "required cities plus the right number
from the tie group" (docs/problem.md, "Required pairs"). -/
def IsNearestChoice (p : Cell) (S : Finset Cell) : Prop :=
  S ⊆ I.cities ∧ S.card = I.k ∧
  (∀ c ∈ S, I.gridDist p c < ⊤) ∧
  (∀ c ∈ S, ∀ c' ∈ I.cities, c' ∉ S → I.gridDist p c ≤ I.gridDist p c')

end Instance

/-- A solution: an undirected network, given as a finite set of cell pairs (each pair
is read in both directions), and the chosen cities of each port. -/
structure Solution where
  edges : Finset (Cell × Cell)
  choice : Cell → Finset Cell

namespace Solution

variable (I : Instance) (σ : Solution)

/-- Adjacency in the built network. -/
def NetAdj (a b : Cell) : Prop := (a, b) ∈ σ.edges ∨ (b, a) ∈ σ.edges

/-- Distinct network neighbours of a cell. -/
noncomputable def neighbours (x : Cell) : Finset Cell :=
  (σ.edges.filter (fun e => e.1 = x)).image Prod.snd ∪
  (σ.edges.filter (fun e => e.2 = x)).image Prod.fst

/-- Track tiles: free cells touched by at least one edge. -/
noncomputable def tiles : Finset Cell :=
  (σ.edges.image Prod.fst ∪ σ.edges.image Prod.snd).filter I.IsFree

/-- `dist_N(p, c)`. -/
noncomputable def netDist (s t : Cell) : ℕ∞ := I.walkDist σ.NetAdj s t

/-- Feasibility (docs/problem.md, "Feasibility"). -/
def Feasible : Prop :=
  (∀ e ∈ σ.edges, I.GridAdj e.1 e.2) ∧
  (∀ x, I.IsFree x → (σ.neighbours x).card ≤ 3) ∧
  (∀ p ∈ I.ports, I.IsNearestChoice p (σ.choice p)) ∧
  (∀ p ∈ I.ports, ∀ c ∈ σ.choice p, σ.netDist I p c < ⊤)

/-- Total excess `Σ (dist_N(p,c) − d(p,c))`. -/
noncomputable def excess : ℕ∞ :=
  ∑ p ∈ I.ports, ∑ c ∈ σ.choice p, (σ.netDist I p c - I.gridDist p c)

/-- Lexicographic cost: (total excess, number of track tiles). -/
noncomputable def cost : Lex (ℕ∞ × ℕ) := toLex (σ.excess I, (σ.tiles I).card)

end Solution

/-- `σ` is an optimal solution of `I`. -/
def IsOptimal (I : Instance) (σ : Solution) : Prop :=
  σ.Feasible I ∧ ∀ τ : Solution, τ.Feasible I → σ.cost I ≤ τ.cost I

/-- Decision version (docs/problem.md): is there a feasible solution with excess `≤ X`
and at most `K` track tiles? -/
def Decide (I : Instance) (X K : ℕ) : Prop :=
  ∃ σ : Solution, σ.Feasible I ∧ σ.excess I ≤ X ∧ (σ.tiles I).card ≤ K

end TrainNetwork
