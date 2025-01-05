import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic


structure Grid (n : Nat) where
  b : Fin n → Fin n → Option ℝ
  antisymm :
    ∀ {u v : Fin n},
      b u v = (b v u).map (λ w => -w)
  /-- susceptances are nonzero if existent-/
  nonzero :
    ∀ {u v : Fin n} (w : ℝ),
      b u v = some w → w ≠ 0
  θ : Fin n → ℝ
  /-- We need the 0 < n hack for some reason, ask ChatGPT :D However node 0 shall be the slack-/
  slack : (h : 0 < n) → θ ⟨0, h⟩ = 0
  /-- Net real power injection (generation - load) at each bus. -/
  p : Fin n → ℝ

  /-- DC power-flow equations:
      For each bus i, the net injection `p i` equals the sum of flows
      to its neighbors:
        ∑ (over j) [b i j * (θ i - θ j)]
      where missing lines (`none`) contribute 0. -/
  dc_equations :
    ∀ i : Fin n,
      p i = ∑ j, (b i j).getD 0 * (θ i - θ j)


/-- The usual Laplacian form of the DC "B" matrix, i.e.
    Bᵢᵢ = ∑ⱼ bᵢⱼ, Bᵢⱼ = -bᵢⱼ for i ≠ j. -/
def laplacian {n: Nat} (G : Grid n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then
      ∑ k, (G.b i k).getD 0
    else
      -((G.b i j).getD 0)

/--Now, Bθ=P should hold, i.e. the Matrix/Vector form should be equivalent to the abovementioned equations-/
theorem laplacian_mul_ThetaVec_eq_PVec {n: Nat} (G : Grid n) :
  (laplacian G).mulVec (G.θ) = G.p := by
  -- We must show equality of two length-`n` vectors,
  -- so it's enough to show equality at each index `i`.
  ext i
  simp only [Matrix.mulVec, dotProduct,
             laplacian, G.dc_equations]
  /-
  Goal now is:

    ∑ x : Fin n,
      (if i = x
        then ∑ k : Fin n, (G.b i k).getD 0
        else - (G.b i x).getD 0
      ) * G.θ x
    = ∑ j : Fin n, (G.b i j).getD 0 * (G.θ i - G.θ j).

  We'll rewrite the LHS by splitting out the "diagonal" term x = i
  from the "off-diagonal" terms x ≠ i.  -/

  -- 1) Separate out the term where x = i from the rest of the sum:
  have splitSum :
    ∑ x, (if i = x then ∑ k, (G.b i k).getD 0 else - (G.b i x).getD 0) * G.θ x
    = (∑ k, (G.b i k).getD 0) * G.θ i
      + ∑ x in Finset.univ.filter (· ≠ i),
          - (G.b i x).getD 0 * G.θ x
  := by /--TODO-/
