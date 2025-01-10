import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin

structure Grid (n : Nat) (l : Nat) where
  b_l : Fin l → ℝ
  l_from : Fin l → Fin n
  l_to : Fin l -> Fin n
  θ : Fin n → ℝ
  p : Fin n → ℝ

/-- We have to assume irreflexivity (no branches leave and end in the same node) as otherwise antisymmetry of b would not hold -/
def loopless {n l : Nat} (G : Grid n l) : Prop :=
  ∀ i : Fin l, G.l_from i ≠ G.l_to i

/-- Define a nodal version of b that sums the branch susceptances between the two nodes -/
def b {n l : ℕ} (G : Grid n l) (n1 n2 : Fin n) : ℝ :=
  ∑ i : Fin l,
    if G.l_from i = n1 ∧ G.l_to i = n2 then
      G.b_l i
    else if G.l_from i = n2 ∧ G.l_to i = n1 then
      - G.b_l i
    else
      0

/-- A helper theorem to get a minus sign into a sum-/
theorem neg_ite {α : Type _} [Ring α] (b : Prop) [Decidable b] (x y : α) :
  - (if b then x else y) = if b then -x else -y := by
  -- Rewrite -z as (-1) * z
  rw [neg_eq_neg_one_mul]
  -- Now pull out (-1) via mul_ite
  rw [mul_ite]
  -- Rewrite (-1)*x as -x and (-1)*y as -y
  simp

/--Prove the antisymmetry of b, will be helpful later to prove the matrix
formulation-/
theorem b_antisym {n l : Nat} (G : Grid n l) (n1 n2 : Fin n) (loopless_local : loopless G) : b G n1 n2 = - b G n2 n1 := by
  simp only [b]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_ite, neg_ite, neg_neg, neg_zero]
  split_ifs with h1 h2
  case pos =>
    -- Here both c1 and c2 are true. Contradiction via loopless.
    cases h1
    rename_i h11 _
    cases h2
    rename_i _ h22
    have : G.l_from i = G.l_to i := by
      rw [← h22] at h11
      exact h11

    apply (loopless_local i) at this
    contradiction
  case neg =>
    rfl
  case pos =>
    rfl
  case neg =>
    rfl

/-- This is eq 1 from the paper-/
def branch_flow {n l : Nat} (G : Grid n l) (line: Fin l) : ℝ :=
  G.b_l line * (G.θ (G.l_from line) - G.θ (G.l_to line))

/-- The kirchhoff current law states that all flows from/to a node need to sum up. This is roughly equal to equation 2 in the paper, though the paper is a bit lax here -/
def kirchhoff {n l : Nat} (G : Grid n l) : Prop :=
  ∀ i : Fin n,
    G.p i = ∑ j : Fin l,
      if G.l_from j = i then
        branch_flow G j
      else if G.l_to j = i then
        -branch_flow G j
      else
        0


/-- These are the nodal power equations as defined in the DC literature
TODO prove -/
def dc_equations {n l : Nat} (G : Grid n l) : Prop :=
    ∀ i : Fin n,
      G.p i = ∑ j : Fin n, (b G i j) * (G.θ i - G.θ j)
