import Mathlib.Algebra.BigOperators.Fin

/-- A helper theorem to get a minus sign into a sum-/
theorem neg_ite {α : Type _} [Ring α] (b : Prop) [Decidable b] (x y : α) :
  - (if b then x else y) = if b then -x else -y := by
  -- Rewrite -z as (-1) * z
  rw [neg_eq_neg_one_mul]
  -- Now pull out (-1) via mul_ite
  rw [mul_ite]
  -- Rewrite (-1)*x as -x and (-1)*y as -y
  simp


theorem if_if_eq_and {α : Type} {A B : Prop} [Decidable A] [Decidable B] (x y : α) :
    (if A then (if B then x else y) else y) = if A ∧ B then x else y := by
  by_cases hA : A
  · -- case A = true
    by_cases hB : B
    · simp [hA, hB]
    · simp [hA, hB]
  · -- case A = false
    simp [hA]
