import InteriorMacro
import WeightedSpectrum

noncomputable section
open JSP404 Real InnerProductGeometry R55.WeightedCollision

namespace R92.Seven

def weights : Fin 4 → ℕ := ![1,2,2,2]
abbrev centers := R90.Interior.c (π/3)

private def tangentAngle : Fin 4 → ℝ := ![0,π/6,π/2,-(π/6)]
def tangent (i : Fin 4) : Point := circleDirection (tangentAngle i)

private theorem ci : Function.Injective centers :=
  R90.Interior.c_injective (by positivity) le_rfl

private theorem norm_coordinates (p : Point) : ‖p‖^2 = p 0*p 0 + p 1*p 1 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]
  rfl

/-- Squared cosine at most one quarter for the tangent versus every actual outgoing chord. -/
theorem projection {i j : Fin 4} (out : i≠0) (ne : i≠j) :
    4 * (inner ℝ (tangent i) (centers j-centers i))^2 ≤ ‖centers j-centers i‖^2 := by
  rw [norm_coordinates]
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [tangent,tangentAngle,centers,R90.Interior.c,circleDirection,
    PiLp.inner_apply,Fin.sum_univ_two,PiLp.sub_apply,Real.cos_pi_div_six,
    Real.sin_pi_div_six,Real.cos_pi_div_three,Real.sin_pi_div_three] <;> nlinarith

private theorem signed_angle {i j : Fin 4} (out : i≠0) (ne : i≠j) (r : ℝ)
    (sign : r = -1 ∨ r=1) : angle (r • tangent i) (centers j-centers i) ≤ 2*π/3 := by
  let u := centers j-centers i
  have pos : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (ci.ne ne.symm))
  have unit : ‖tangent i‖=1 := norm_circleDirection _
  have length : |2 * inner ℝ (tangent i) u| ≤ ‖u‖ := by
    rw [← abs_of_nonneg (le_of_lt pos)]
    apply sq_le_sq.mp
    have p:=projection out ne
    change 4*(inner ℝ (tangent i) u)^2 ≤ ‖u‖^2 at p
    nlinarith
  have lo:= (abs_le.mp length).1
  have hi:= (abs_le.mp length).2
  have lower : -(1/2 : ℝ) ≤ inner ℝ (r • tangent i) u / (‖r • tangent i‖*‖u‖) := by
    rcases sign with rfl|rfl <;>
      simp only [neg_one_smul,one_smul,norm_neg,unit,one_mul,inner_neg_left] <;>
      apply (le_div_iff₀ pos).mpr <;> linarith
  have flip : cos (2*π/3) = -(1/2:ℝ) := by
    rw [show 2*π/3=π-π/3 by ring, cos_pi_sub,cos_pi_div_three]
  change arccos _ ≤ _
  calc _ ≤ arccos (-(1/2:ℝ)) := arccos_le_arccos lower
       _ = 2*π/3 := by rw [←flip,arccos_cos (by positivity) (by linarith [pi_pos])]

theorem attainable_seven :
    2*π/3 ∈ attainable weights centers := by
  have wp (i : Fin 4) : 0 < weights i := by fin_cases i <;> decide
  have small (i : Fin 4) : dim weights i ≤ 1 := by fin_cases i <;> decide
  have mac : Macro centers (2*π/3) := by
    rw [show 2*π/3=π-π/3 by ring]
    exact R90.Interior.macro (by positivity) le_rfl
  apply admissible_mem wp ci
  let v (i : Fin 4) (_ : Fin (dim weights i)) := tangent i
  refine ⟨by positivity, mac, v, (fun _ _ => norm_circleDirection _), ?_, ?_⟩
  · intro i p q ne
    have h:=small i
    have hp:=p.isLt
    have hq:=q.isLt
    exact (ne (Fin.ext (by omega))).elim
  · intro i j ne p r hr
    have nz : i≠0 := by
      rintro rfl
      have e : dim weights 0 = 0 := by decide
      have hp:=p.isLt
      omega
    exact signed_angle nz ne r hr

theorem total_seven : ∑ i, weights i = 7 := by decide

end R92.Seven

#print axioms R92.Seven.projection
#print axioms R92.Seven.attainable_seven
#print axioms R92.Seven.total_seven
