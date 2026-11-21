import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! Arithmetic step of the Euclidean angle argument for a vertex with
the maximum odd number of sign changes. Angles are in units of the
defect and T is the angle sum of one planar triangle in these units. -/
namespace FullSwitchTriangle

def Band (m : Nat) (T theta : ℝ) : Prop :=
  ∃ j : Nat, 2 * (j : ℝ) ≤ theta ∧ theta ≤ 2 * (j : ℝ) + (T - (m : ℝ))

theorem no_triangle {m : Nat} (hm : m % 2 = 1) {T x y z : ℝ}
    (width : T - (m : ℝ) < 1/2) (sum : x + y + z = T)
    (hx : Band m T x) (hy : Band m T y) (hz : Band m T z) : False := by
  obtain ⟨i, il, iu⟩ := hx
  obtain ⟨j, jl, ju⟩ := hy
  obtain ⟨k, kl, ku⟩ := hz
  let K := 2 * (i + j + k)
  have ev : K % 2 = 0 := by dsimp [K]; omega
  have coeK : (K : ℝ) = 2 * ((i : ℝ) + j + k) := by
    simp [K, Nat.cast_add, Nat.cast_mul]
  have lower : (m : ℝ) - 1 < K := by rw [coeK]; linarith
  have upper : (K : ℝ) < m + 1 := by rw [coeK]; linarith
  have eq : K = m := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have d : K + 1 ≤ m := by omega
      have de : (K : ℝ) + 1 ≤ m := by exact_mod_cast d
      linarith
    · have d : m + 1 ≤ K := by omega
      have de : (m : ℝ) + 1 ≤ K := by exact_mod_cast d
      linarith
  omega

/-- Stratum bounds for a set avoiding 9π/11. The parameter r is the
angular defect divided by the five-bin width π/5. -/
theorem five_bin_count {h i j : Nat} {r : ℝ} (hr : 10/11 < r)
    (hull : h ≤ 10) (middle : (i : ℝ) * (3*r-2) ≤ 20) (top : j ≤ 2) :
    h + i + j ≤ 39 := by
  have hi : i ≤ 27 := by
    by_contra! hn
    have hn28 : 28 ≤ i := by omega
    have hN : (28 : ℝ) ≤ i := by exact_mod_cast hn28
    have hR : 0 < 3*r-2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hR.le]
  omega

#print axioms no_triangle
#print axioms five_bin_count
end FullSwitchTriangle
