import Mathlib
import Mathlib.Data.Matrix.Basic


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
      p i = ∑ j, (b i j).elim 0 (fun x => x * (θ i - θ j))


def BMatrix (G : Grid n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (G.b i j).getD 0
