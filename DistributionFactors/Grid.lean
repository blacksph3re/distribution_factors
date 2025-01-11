import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset
import DistributionFactors.Helper

structure Grid (n : Nat) (e : Nat) where
  b_e: Fin e → ℝ
  e_from : Fin e → Fin n
  e_to : Fin e -> Fin n
  θ : Fin n → ℝ
  p : Fin n → ℝ

namespace Grid

/-- We have to assume irreflexivity (no branches leave and end in the same node) as otherwise antisymmetry of b would not hold -/
def loopless {n e: Nat} (G : Grid n e) : Prop :=
  ∀ i : Fin e, G.e_from i ≠ G.e_to i

/--Without loss of generality we can assume no zero-susceptance branches are present in the grid (i.e. switches are merged)-/
def b_nonzero {n e: Nat} (G : Grid n e) : Prop :=
  ∀ i : Fin e, G.b_e i ≠ 0

/-- Furthermore we assume the grid to be balanced in some equations, i.e. the injections add up. An alternative to this assumption is the slack assumption -/
def balanced {n e : Nat} (G : Grid n e) : Prop :=
  ∑ i : Fin n, G.p i = 0

/-- Define a nodal version of b that sums the branch susceptances between the two nodes -/
def b {n e : ℕ} (G : Grid n e) (n1 n2 : Fin n) : ℝ :=
  ∑ i : Fin e,
    if G.e_from i = n1 ∧ G.e_to i = n2 then
      G.b_e i
    else if G.e_from i = n2 ∧ G.e_to i = n1 then
      - G.b_e i
    else
      0

/--Prove that b from n1 n1 is equal to zero-/
theorem b_id_eq_zero {n e : Nat} (G : Grid n e) (n1 : Fin n) (loopless_local : loopless G) : b G n1 n1 = 0 := by
  rw [loopless] at loopless_local
  rw [b]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with h1
  .
    cases h1
    rename_i ha hb
    rw [← hb] at ha
    apply loopless_local at i
    contradiction
  .
    rfl


/--Prove the antisymmetry of b, will be helpful later to prove the matrix
formulation-/
theorem b_antisym {n e : Nat} (G : Grid n e) (n1 n2 : Fin n) (loopless_local : loopless G) : b G n1 n2 = - b G n2 n1 := by
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
    have hc: G.e_from i = G.e_to i := by
      rw [← h22] at h11
      exact h11

    apply (loopless_local i) at hc
    contradiction
  case neg =>
    rfl
  case pos =>
    rfl
  case neg =>
    rfl

/-- This is eq 1 from the paper-/
def e_p {n e : Nat} (G : Grid n e) (edge: Fin e) : ℝ :=
  G.b_e edge * (G.θ (G.e_from edge) - G.θ (G.e_to edge))

/-- The kirchhoff current law states that all flows from/to a node need to sum up. This is roughly equal to equation 2 in the paper, though the paper is a bit lax here -/
def kirchhoff {n e : Nat} (G : Grid n e) : Prop :=
  ∀ i : Fin n,
    G.p i = ∑ j : Fin e,
      if G.e_from j = i then
        e_p G j
      else if G.e_to j = i then
        -e_p G j
      else
        0

/-- Define the node-edge incidence matrix as in equation 3-/
def node_edge_incidence {n e : Nat} (G : Grid n e) : Matrix (Fin n) (Fin e) ℝ :=
  fun (node: Fin n) (edge: Fin e) =>
    if G.e_from edge = node then
      1
    else if G.e_to edge = node then
      -1
    else
      0

def diagonal_b {n e : Nat} (G : Grid n e) : Matrix (Fin e) (Fin e) ℝ :=
  fun (edge1: Fin e) (edge2 : Fin e) =>
    if edge1 = edge2 then
      G.b_e edge1
    else
      0

/-- Prove equation 4 -/
theorem branch_flow_vec_eq_branch_flow {n e : Nat} (G : Grid n e) : ∀ edge : Fin e, e_p G edge = (Matrix.mulVec (G.diagonal_b * G.node_edge_incidence.transpose) G.θ) edge := by
  intro e1
  rw [e_p, Matrix.mulVec, Matrix.transpose]
