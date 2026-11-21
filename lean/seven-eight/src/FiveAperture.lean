import GapFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
noncomputable section
namespace R64.Five
open Real

private theorem local_trig {x : ℝ} (xp : 0≤x) (one : x≤1) :
    sin x≤x ∧ x-x^3/5≤sin x ∧ 1-3*x^2/5≤cos x ∧ cos x≤1-2*x^2/5 := by
  have sb:=Real.sin_bound (x:=x) (by rwa [abs_of_nonneg xp])
  have cb:=Real.cos_bound (x:=x) (by rwa [abs_of_nonneg xp])
  rw [abs_of_nonneg xp,abs_le] at sb cb
  have sq : x^2≤1 := by nlinarith [mul_self_le_mul_self xp one]
  have e5 : x^5≤x^3 := by nlinarith only [mul_le_mul_of_nonneg_right sq (pow_nonneg xp 3)]
  have e4 : x^4≤x^2 := by nlinarith only [mul_le_mul_of_nonneg_right sq (sq_nonneg x)]
  obtain ⟨sl,su⟩:=sb
  obtain ⟨cl,cu⟩:=cb
  exact ⟨by nlinarith [pow_nonneg xp 3],by nlinarith [pow_nonneg xp 3],
    by nlinarith [sq_nonneg x],by nlinarith [sq_nonneg x]⟩

private theorem one_lt_half_pi : (1:ℝ)<π/2 := by
  by_contra! bad
  have c := (local_trig pi_div_two_pos.le bad).2.2.1
  rw [cos_pi_div_two] at c
  nlinarith [mul_self_le_mul_self pi_div_two_pos.le bad]

theorem atan_upper {u : ℝ} (up : 0≤u) (hi : u≤1) : arctan u≤u := by
  have inside : u<π/2 := by linarith [one_lt_half_pi]
  have cp : 0<cos u := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],inside⟩
  have h:=local_trig up hi
  have ap : u≤tan u := by
    rw [tan_eq_sin_div_cos,le_div_iff₀ cp]
    nlinarith only [mul_le_mul_of_nonneg_left h.2.2.2 up,h.2.1,pow_nonneg up 3]
  simpa [arctan_tan (by linarith [pi_pos] : -(π/2)<u) inside] using arctan_le_arctan_iff.mpr ap

theorem atan_lower {u : ℝ} (up : 0<u) (small : (16/17:ℝ)*u≤1/4) :
    (16/17:ℝ)*u<arctan u := by
  let x:ℝ:=(16/17)*u
  have xp : 0<x := by dsimp [x];positivity
  change x≤1/4 at small
  have inside : x<π/2 := by linarith [one_lt_half_pi]
  have cp : 0<cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],inside⟩
  have h:=local_trig xp.le (by linarith)
  have c : (16/17:ℝ)<cos x := by
    nlinarith [mul_self_le_mul_self xp.le small,h.2.2.1]
  have tanlt : tan x<u := by
    rw [tan_eq_sin_div_cos,div_lt_iff₀ cp]
    have e : x=(16/17:ℝ)*u := rfl
    nlinarith only [h.1,mul_lt_mul_of_pos_right c up,e]
  simpa [arctan_tan (by linarith [pi_pos] : -(π/2)<x) inside] using arctan_lt_arctan_iff.mpr tanlt

/-- The aperture between headings on opposite sides of the horizontal
exceeds one defect when their dimensionless slope separation is at least 17/16. -/
theorem separated {l a b : ℝ} (lp : 0<l) (sm : l≤1/4) (lo : -(17/16)≤a) (az : a≤0)
    (bz : 0≤b) (hi : b≤17/16) (dist : 17/16≤b-a) :
    l<arctan (l*b)-arctan (l*a) := by
  have weak {x : ℝ} (xp : 0≤x) (ub : x≤17/16) : (16/17:ℝ)*(l*x)≤arctan (l*x) := by
    rcases eq_or_lt_of_le xp with e|gt
    · simp [←e]
    · apply (atan_lower (mul_pos lp gt) _).le
      nlinarith only [mul_le_mul_of_nonneg_left ub lp.le,sm]
  have strict {x : ℝ} (xp : 0<x) (ub : x≤17/16) : (16/17:ℝ)*(l*x)<arctan (l*x) := by
    apply atan_lower (mul_pos lp xp)
    nlinarith only [mul_le_mul_of_nonneg_left ub lp.le,sm]
  have n : arctan (l*(-a))= -arctan (l*a) := by rw [mul_neg,arctan_neg]
  have d:=mul_le_mul_of_nonneg_left dist lp.le
  rcases eq_or_lt_of_le bz with e|gt
  · have xs:=strict (x:=-a) (by linarith) (by linarith)
    rw [n] at xs
    simp [←e] at xs ⊢
    nlinarith
  · have xs:=weak (x:=-a) (by linarith) (by linarith)
    rw [n] at xs
    nlinarith only [xs,strict gt hi,d]

#print axioms separated
end R64.Five