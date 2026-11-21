import FourSeparated
noncomputable section
namespace R52.ThreeCover
open JSP404

/-- The three disk centers may be arbitrary plane points, repeated, or vary with each approximation.
Using any pair in S as the length scale is equivalent to permitting its diameter. -/
def Covered (S : Finset Point) (δ : ℝ) := ∃ p∈S, ∃ q∈S, p≠q ∧
  ∃ c : Fin 3→Point, ∀ x∈S, ∃ i, dist x (c i)≤δ*dist p q

def scores (N : ℕ) : Set ℝ := {u | ∀ δ : ℝ, 0<δ → ∃ S : Finset Point,
  S.card=N ∧ maxAngle S<u+δ ∧ Covered S δ}

end R52.ThreeCover
