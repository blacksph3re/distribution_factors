import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-- A helper theorem to get a minus sign into a sum-/
theorem neg_ite {α : Type _} [Ring α] (b : Prop) [Decidable b] (x y : α) :
  - (if b then x else y) = if b then -x else -y := by
  -- Rewrite -z as (-1) * z
  rw [neg_eq_neg_one_mul]
  -- Now pull out (-1) via mul_ite
  rw [mul_ite]
  -- Rewrite (-1)*x as -x and (-1)*y as -y
  simp


/--A helper theorem that a nested if can be un-nested-/
theorem if_if_eq_and {α : Type} {A B : Prop} [Decidable A] [Decidable B] (x y : α) :
    (if A then (if B then x else y) else y) = if A ∧ B then x else y := by
  by_cases hA : A
  · -- case A = true
    by_cases hB : B
    · simp [hA, hB]
    · simp [hA, hB]
  · -- case A = false
    simp [hA]

/--If a sum is only non-zero in two points, this is helpful. Kind of like Finset.sum_eq_single but with two points.-/
theorem sum_two_points {α β: Type*} [AddCommMonoid β] [Fintype α] [DecidableEq α] (a b : α) (fa fb: α → β) (ha: a ≠ b) : ∑ x : α, (if x = a then fa x else if x = b then fb x else 0) = fa a + fb b := by
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ a)]
  simp
  have hb : b ∈ Finset.univ \ {a} := by
    simp [Finset.mem_univ, Finset.mem_sdiff, Finset.mem_singleton, eq_comm]
    simp at ha
    exact ha
  rw [Finset.sum_eq_sum_diff_singleton_add hb]
  simp at ha
  rw [eq_comm] at ha
  simp [if_neg ha]
  rw [Finset.sum_eq_zero]
  . simp [add_comm]
  . simp
    intro z hx hy
    simp [hx, hy]


theorem matrix_mul_vec_assoc {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (v : (Fin p) → ℝ) :
  ((A * B).mulVec v) = A.mulVec (B.mulVec v) := by
  ext i
  simp [dotProduct_assoc]
