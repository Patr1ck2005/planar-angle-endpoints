import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Linarith

namespace TwoAnchorGeometry
open Real
open scoped RealInnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def ray (s : ℝ) : Plane := !₂[cos s, sin s]

private theorem norm_ray (s : ℝ) : ‖ray s‖=1 := by
  have h := EuclideanSpace.real_norm_sq_eq (ray s)
  rw [Fin.sum_univ_two] at h
  change ‖ray s‖^2 = cos s ^ 2 + sin s ^ 2 at h
  nlinarith [Real.sin_sq_add_cos_sq s,norm_nonneg (ray s)]

private theorem inner_ray (r s : ℝ) : inner ℝ (ray r) (ray s) = cos (r-s) := by
  rw [PiLp.inner_apply,Fin.sum_univ_two,Real.cos_sub]
  change cos s * cos r + sin s * sin r = _
  ring

/-- Difference of two upper-half-plane bearings is the actual Euclidean
vector angle after taking its absolute value. -/
theorem angle_rays {r s : ℝ} (hr : 0≤r ∧ r≤π) (hs : 0≤s ∧ s≤π) :
    InnerProductGeometry.angle (ray r) (ray s) = |r-s| := by
  rw [InnerProductGeometry.angle,inner_ray,norm_ray,norm_ray,one_mul,div_one]
  rw [←Real.cos_abs (r-s)]
  exact Real.arccos_cos (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)

/-- AC and BC point in the opposite directions to the upper bearings a
and π−b. Both inequalities below are ordinary mathlib Euclidean angles. -/
theorem upward_chord_interval {a b u lam : ℝ}
    (ha : 0<a ∧ a<lam) (hb : 0<b ∧ b<lam) (hlam : lam≤π)
    (hu : 0≤u ∧ u≤π)
    (hA : InnerProductGeometry.angle (ray u) (-(ray a)) ≤ π-lam)
    (hB : InnerProductGeometry.angle (ray u) (-(ray (π-b))) ≤ π-lam) :
    lam+a ≤ u ∧ u ≤ π-lam-b := by
  rw [InnerProductGeometry.angle_neg_right,angle_rays hu ⟨by linarith,by linarith⟩] at hA
  rw [InnerProductGeometry.angle_neg_right,angle_rays hu ⟨by linarith,by linarith⟩] at hB
  constructor
  · rcases le_total a u with h | h
    · rw [abs_of_nonneg (by linarith)] at hA
      linarith
    · rw [abs_of_nonpos (by linarith)] at hA
      linarith
  · rcases le_total u (π-b) with h | h
    · rw [abs_of_nonpos (by linarith)] at hB
      linarith
    · rw [abs_of_nonneg (by linarith)] at hB
      linarith

/-- With minimum anchor bearings a₀,b₀ and a₀+b₀≥λ, all admissible
upward chord bearings belong to one interval shorter than (n−2)λ. -/
theorem common_interval {I : Type*} (a b u : I → ℝ) (a₀ b₀ lam : ℝ)
    (hlam : 0<lam) (hpi : lam≤π) (hn : 2≤⌊π/lam⌋₊) (hab : lam≤a₀+b₀)
    (hmin : ∀ i, a₀≤a i ∧ b₀≤b i)
    (ha : ∀ i, 0<a i ∧ a i<lam) (hb : ∀ i, 0<b i ∧ b i<lam)
    (hu : ∀ i, 0≤u i ∧ u i≤π)
    (hA : ∀ i, InnerProductGeometry.angle (ray (u i)) (-(ray (a i))) ≤ π-lam)
    (hB : ∀ i, InnerProductGeometry.angle (ray (u i)) (-(ray (π-b i))) ≤ π-lam) :
    (∀ i, lam+a₀≤u i ∧ u i≤π-lam-b₀) ∧
      (π-lam-b₀)-(lam+a₀) < ((⌊π/lam⌋₊-2:Nat):ℝ)*lam := by
  constructor
  · intro i
    have h := upward_chord_interval (ha i) (hb i) hpi (hu i) (hA i) (hB i)
    have := hmin i
    exact ⟨by linarith,by linarith⟩
  · rw [Nat.cast_sub hn,Nat.cast_ofNat]
    have h := (div_lt_iff₀ hlam).mp (Nat.lt_floor_add_one (π/lam))
    nlinarith

#print axioms angle_rays
#print axioms upward_chord_interval
#print axioms common_interval

/-- The determinants of the two supporting lines, with A=(0,0) and
B=(1,0), give strict increase of both ratios in the open vertical strip. -/
theorem ratios_of_above_lines {xC yC xD yD : ℝ}
    (hc : 0<xC ∧ xC<1) (hd : 0<xD ∧ xD<1)
    (hA : 0 < xC*(yD-yC)-yC*(xD-xC))
    (hB : 0 < yC*(xD-xC)-(xC-1)*(yD-yC)) :
    yC/xC < yD/xD ∧ yC/(1-xC) < yD/(1-xD) := by
  constructor
  · apply (div_lt_div_iff₀ hc.1 hd.1).2
    nlinarith
  · apply (div_lt_div_iff₀ (by linarith : 0<1-xC) (by linarith : 0<1-xD)).2
    nlinarith

/-- Actual signed-ray data imply the two increasing anchor inclinations.
rA, rB, r are the positive distances AC, BC and CD respectively.
No supporting-line or slope inequality is an extra hypothesis. -/
theorem anchor_inclinations_increase {xC yC xD yD a b u lam rA rB r : ℝ}
    (hc : 0<xC ∧ xC<1) (hd : 0<xD ∧ xD<1)
    (hr : 0<rA ∧ 0<rB ∧ 0<r)
    (hAC : xC=rA*cos a ∧ yC=rA*sin a)
    (hBC : 1-xC=rB*cos b ∧ yC=rB*sin b)
    (hCD : xD-xC=r*cos u ∧ yD-yC=r*sin u)
    (ha : 0<a ∧ a<lam) (hb : 0<b ∧ b<lam) (hlam : lam≤π)
    (hu : 0≤u ∧ u≤π)
    (hA : InnerProductGeometry.angle (ray u) (-(ray a)) ≤ π-lam)
    (hB : InnerProductGeometry.angle (ray u) (-(ray (π-b))) ≤ π-lam) :
    Real.arctan (yC/xC) < Real.arctan (yD/xD) ∧
    Real.arctan (yC/(1-xC)) < Real.arctan (yD/(1-xD)) := by
  have hangle := upward_chord_interval ha hb hlam hu hA hB
  have sA := Real.sin_pos_of_pos_of_lt_pi (x:=u-a) (by linarith) (by linarith)
  have sB := Real.sin_pos_of_pos_of_lt_pi (x:=u+b) (by linarith) (by linarith)
  have hlineA : 0 < xC*(yD-yC)-yC*(xD-xC) := by
    have he : xC*(yD-yC)-yC*(xD-xC) = (rA*r)*sin (u-a) := by
      rw [hCD.1,hCD.2,hAC.1,hAC.2,Real.sin_sub]
      ring
    rw [he]
    exact mul_pos (mul_pos hr.1 hr.2.2) sA
  have hlineB : 0 < yC*(xD-xC)-(xC-1)*(yD-yC) := by
    have he : yC*(xD-xC)-(xC-1)*(yD-yC) = (rB*r)*sin (u+b) := by
      rw [hCD.1,hCD.2,show xC-1=-(1-xC) by ring,hBC.1,hBC.2,Real.sin_add]
      ring
    rw [he]
    exact mul_pos (mul_pos hr.2.1 hr.2.2) sB
  obtain ⟨hleft,hright⟩ := ratios_of_above_lines hc hd hlineA hlineB
  exact ⟨Real.arctan_strictMono hleft, Real.arctan_strictMono hright⟩

#print axioms ratios_of_above_lines
#print axioms anchor_inclinations_increase

end TwoAnchorGeometry
