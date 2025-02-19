import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
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
  case pos =>
    cases h1
    rename_i ha hb
    rw [← hb] at ha
    apply loopless_local at i
    contradiction
  case neg =>
    rfl


/--Prove the antisymmetry of b, will be hopefully helpful later to prove the matrix formulation-/
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

/-- Define a nodal version of e_p that sums all power from node n1 to n2. We define this similar to b, i.e. we are not taking into account nodal injections and only sum branch flows. -/
def n_p {n e : Nat} (G : Grid n e) (n1 n2 : Fin n) : ℝ :=
  ∑ i : Fin e,
    if G.e_from i = n1 ∧ G.e_to i = n2 then
      G.e_p i
    else if G.e_from i = n2 ∧ G.e_to i = n1 then
      - G.e_p i
    else
      0

/-- Just as b, n_p for the same node is zero, same proof as for b -/
theorem n_p_id_eq_zero {n e : Nat} (G: Grid n e) (n1: Fin n) (loopless_local: loopless G) : n_p G n1 n1 = 0 := by
  rw [n_p]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with h1
  case pos =>
    cases h1
    rename_i ha hb
    rw [← hb] at ha
    apply loopless_local at i
    contradiction
  case neg =>
    rfl

/-- n_p is also antisymmetric, same proof as for b -/
theorem n_p_antisym {n e : Nat} (G: Grid n e) (n1 n2 : Fin n) (loopless_local: loopless G) : n_p G n1 n2 = -n_p G n2 n1 := by
  simp only [n_p]
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

/-- nodal_branch_sum sums up all the flows leaving or entering the node via branches. If kirchhoff holds, this should be equivalent to the injection at
the station-/
def nodal_branch_sum {n e : ℕ} (G: Grid n e) (n1: Fin n) : ℝ :=
  ∑ j : Fin e,
    if G.e_from j = n1 then
      e_p G j
    else if G.e_to j = n1 then
      -e_p G j
    else
      0

/--Now we prove that the nodal_branch_sum is the same as using n_p and summing over n2. This is helpful to create a second form of the kirchhoff that uses n_p-/
theorem nodal_branch_sum_eq_sum_n_p {n e : Nat} (G: Grid n e) (loopless_local: loopless G) : ∀ n1 : Fin n, nodal_branch_sum G n1 = ∑ n2 : Fin n, n_p G n1 n2 := by
  simp only [n_p, nodal_branch_sum]
  intro nx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ex
  split_ifs with h1 h2
  case pos =>
    have h3: G.e_to ex ≠ nx := by
      rw [loopless] at loopless_local
      have h := loopless_local ex
      rw [h1] at h
      exact h.symm
    rw [h1]
    simp
    have h4: ∀ x, (if G.e_to ex = x then G.e_p ex
                 else if nx = x ∧ G.e_to ex = nx then -G.e_p ex
                 else 0)
           = if x = G.e_to ex then G.e_p ex else 0 := by
      intro x
      by_cases c: G.e_to ex = x
      . simp [c]
      . rw [if_neg c]
        by_cases d : (nx = x ∧ G.e_to ex = nx)
        . cases d
          contradiction
        . rw [eq_comm] at c
          simp [d, c]
    simp [h4]
  case neg =>
    intro _
    rw [eq_comm]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg, if_neg]
    intro c
    rcases c
    contradiction
    rw [and_comm]
    intro c
    rcases c
    contradiction
  case pos =>
    rw [h2]
    simp
    simp [h1]


/-- The kirchhoff current law states that all flows from/to a node plus the injection need to sum to zero. This is roughly equal to equation 2 in the paper, though the paper is a bit lax here -/
def kirchhoff {n e : Nat} (G : Grid n e) : Prop :=
  ∀ i : Fin n,
    G.p i = nodal_branch_sum G i

-- We can write the kirchhoff law in a nodal version using our nodal_branch_sum_eq_sum_n_p theorem
theorem nodal_kirchhoff {n e : Nat} (G: Grid n e) (kirchhoff_local: kirchhoff G) (loopless_local: loopless G) : ∀ i : Fin n, G.p i = ∑ j : Fin n, n_p G i j := by
  intro i
  rw [← nodal_branch_sum_eq_sum_n_p]
  rw [kirchhoff_local]
  apply loopless_local


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
theorem branch_flow_vec_eq_branch_flow {n e : Nat} (G : Grid n e) (loopless_local: loopless G): e_p G = ((G.diagonal_b * G.node_edge_incidence.transpose).mulVec G.θ) := by
  ext edge
  -- Unfold the matrix product and mulVec into their sum‐of‐products form:
  simp [Matrix.mulVec, Matrix.transpose, Matrix.mul_apply, diagonal_b, node_edge_incidence, dotProduct, e_p, eq_comm, neg_ite, if_if_eq_and]
  have h1 : (∀ x : Fin n, (∑ x_1 : Fin e,
        if x = G.e_from x_1 then if edge = x_1 then G.b_e edge else 0
        else if x = G.e_to x_1 ∧ edge = x_1 then -G.b_e edge else 0) = if x = G.e_from edge then G.b_e edge else if x = G.e_to edge then -G.b_e edge else 0) := by
    intro x
    rw [Finset.sum_eq_single edge]
    . simp
    . intro x_l _ h2
      simp [eq_comm] at h2
      simp [h2]
    . simp
  simp [h1]
  -- the sum is only non-zero in two spots
  rw [sum_two_points (G.e_from edge) (G.e_to edge)]
  case ha =>
    rw [loopless] at loopless_local
    simp [loopless_local]
  simp [mul_sub, mul_neg, ← sub_eq_add_neg]

/--Equation 5 from the paper. I am a bit disappointed that I didn't need my nodal kirchhoff version...-/
theorem kirchhoff_matrix {n e : ℕ} (G : Grid n e) (kirchhoff_local: kirchhoff G) : G.p = Matrix.mulVec G.node_edge_incidence G.e_p := by
  ext i
  simp [Matrix.mulVec, node_edge_incidence, dotProduct]
  simp [kirchhoff, nodal_branch_sum] at kirchhoff_local
  simp [kirchhoff_local]

/--Equation 6 (the first half), which is just replacing in equation 4 and 5.-/
theorem kirchhoff_theta {n e : ℕ} (G : Grid n e) (kirchhoff_local: kirchhoff G) (loopless_local: loopless G): G.p = (G.node_edge_incidence * G.diagonal_b * G.node_edge_incidence.transpose).mulVec G.θ := by
  ext x
  rw [Matrix.mul_assoc G.node_edge_incidence G.diagonal_b G.node_edge_incidence.transpose]
  rw [matrix_mul_vec_assoc]
  rw [← branch_flow_vec_eq_branch_flow]
  case loopless_local =>
    exact loopless_local
  rw [kirchhoff_matrix]
  case kirchhoff_local =>
    simp [kirchhoff_local]

/--Define the slackless B matrix-/
def nodal_susceptance_matrix_full {n e : ℕ} (G : Grid n e) : Matrix (Fin n) (Fin n) ℝ :=
  fun (n1: Fin n) (n2 : Fin n) =>
    if n1 = n2 then
      ∑ n3 : Fin n, G.b n1 n3
    else
      - G.b n1 n2


/--Equation 7 (aka B is equivalent to the nodal susceptance definition given in the paper). This will also trivially prove the second half of equation 6-/
theorem nodal_susceptance_matrix_eq_B {n e : ℕ} (G : Grid n e) : G.nodal_susceptance_matrix_full = G.node_edge_incidence * G.diagonal_b * G.node_edge_incidence.transpose := by
  ext n1 n2
  simp [nodal_susceptance_matrix_full, Matrix.transpose, Matrix.mul_apply, node_edge_incidence, diagonal_b, neg_ite]
  by_cases h : n1=n2
  case pos => -- First prove the diagonal
    simp [h]
