import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset
import DistributionFactors.Helper
import DistributionFactors.Grid

/-- These are the nodal power equations as defined in the DC literature
 TODO prove -/
theorem dc_equations {n l : Nat} (G : Grid n l) (loopless_local : loopless G) (kirchhoff_local : kirchhoff G) (b_nonzero_local : b_nonzero G) : ∀ i : Fin n, G.p i = ∑ j : Fin n, (b G i j) * (G.θ i - G.θ j) := by
  intro i
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  have id_b_zero : b G i i * (G.θ i - G.θ i) = 0 := by
    rw [sub_self, mul_zero]
  rw [id_b_zero, zero_add]
  rw [kirchhoff_local]
  simp only [b, l_p]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro line _
  split_ifs with h_from h_to
  case pos =>
    rw [h_from]
    simp
    rw [Finset.sum_eq_single (G.l_to line)]
    case h₀ =>
      intro to_node _ h
      symm at h
      split_ifs
      .
        contradiction
      .
        rename_i _ h2
        cases h2
        rename_i _ h4
        rw [← h4] at h_from
        rw [loopless] at loopless_local
        apply loopless_local at line
        contradiction
      .
        rfl
    case h₁ =>
      simp
    simp
  case pos =>
    simp [*]
