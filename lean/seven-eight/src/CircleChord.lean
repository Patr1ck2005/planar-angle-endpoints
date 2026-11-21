import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Ray
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Sendov.CircleChord

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def point (u : ℝ) : Plane := !₂[Real.cos u, Real.sin u]

noncomputable def tangent (u : ℝ) : Plane := !₂[-Real.sin u, Real.cos u]

/-- The parametrized point belongs to the Euclidean unit circle. -/
theorem point_norm (a : ℝ) : ‖point a‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  change Real.sqrt (‖Real.cos a‖ ^ 2 + ‖Real.sin a‖ ^ 2) = 1
  simp only [Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq, Real.sqrt_one]


/-- Chord factorization in the actual Euclidean plane. -/
theorem chord_factor (u v : ℝ) :
    point v - point u = (2 * Real.sin ((v-u)/2)) • tangent ((v+u)/2) := by
  ext i
  fin_cases i
  · change Real.cos v - Real.cos u = 2 * Real.sin ((v-u)/2) * (-Real.sin ((v+u)/2))
    rw [Real.cos_sub_cos]
    ring
  · change Real.sin v - Real.sin u = 2 * Real.sin ((v-u)/2) * Real.cos ((v+u)/2)
    exact Real.sin_sub_sin v u

theorem chord_scale_pos {u v : ℝ} (huv : u < v) (hwrap : v-u < 2*Real.pi) :
    0 < 2 * Real.sin ((v-u)/2) := by
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem tangent_eq_point_quarter (a : ℝ) : tangent a = point (a + Real.pi/2) := by
  ext i
  fin_cases i
  · exact (Real.cos_add_pi_div_two a).symm
  · exact (Real.sin_add_pi_div_two a).symm

/-- For ordered lifts through one turn, the directed chord, not just its
unoriented line, is on the ray at the half-sum plus a quarter turn. -/
theorem chord_sameRay {u v : ℝ} (huv : u < v) (hwrap : v-u < 2*Real.pi) :
    SameRay ℝ (point v - point u) (point ((v+u)/2 + Real.pi/2)) := by
  rw [chord_factor, tangent_eq_point_quarter]
  exact SameRay.sameRay_pos_smul_left _ (chord_scale_pos huv hwrap)

/-- The chord's projective representative as a real linear subspace. -/
theorem chord_span {u v : ℝ} (huv : u < v) (hwrap : v-u < 2*Real.pi) :
    Submodule.span ℝ {point v - point u} =
      Submodule.span ℝ {point ((v+u)/2 + Real.pi/2)} := by
  rw [chord_factor, tangent_eq_point_quarter]
  apply Submodule.span_singleton_smul_eq
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (chord_scale_pos huv hwrap))

#print axioms chord_factor
#print axioms chord_sameRay
#print axioms chord_span
end Sendov.CircleChord
