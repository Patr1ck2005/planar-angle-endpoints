import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

noncomputable section
namespace R53.TwoAnchor
open Real InnerProductGeometry

/-- Quotient form of the Euclidean angle (the pinned mathlib complex-angle identity). -/
theorem quotient_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    angle x y = |(x / y).arg| := by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (Complex.abs_arg_le_pi _) ?_
  rw [Real.cos_abs, Complex.cos_arg (div_ne_zero hx hy)]
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field

theorem one_angle {y : ℂ} (hy : y≠0) : angle 1 y=|y.arg| := by
  simp [quotient_angle,hy]

theorem angle_mul_right {r : ℂ} (hr : r≠0) (x y : ℂ) :
    angle (x*r) (y*r)=angle x y := by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [quotient_angle, mul_div_mul_right, *]

/-- Signed arguments in one open right half-plane measure the actual angle. -/
theorem angle_in_strip {z w : ℂ} (hz : z≠0) (hw : w≠0)
    (h : -π < z.arg-w.arg ∧ z.arg-w.arg ≤ π) :
    angle z w = |z.arg-w.arg| := by
  rw [quotient_angle hz hw]
  congr 1
  rw [← Complex.arg_coe_angle_toReal_eq_arg (z/w),Complex.arg_div_coe_angle hz hw,
    ← Real.Angle.coe_sub,Real.Angle.toReal_coe_eq_self_iff.mpr h]

/-- Two narrow anchor fans forbid opposite-side ordinary points.  In the
complex chart the anchors are 0 and 1. All hypotheses are actual vector angles. -/
theorem chart_side {I : Type*} (z : I → ℂ) {lam : ℝ} (hl : 0<lam) (hlπ : lam≤π/2)
    (zeroN : ∀ i, z i≠0) (oneN : ∀ i, z i≠1)
    (narrowA : ∀ i, angle 1 (z i)<lam)
    (narrowB : ∀ i, angle 1 (1-z i)<lam)
    (cap : ∀ i, angle (-(z i)) (1-z i)≤π-lam)
    (pairA : ∀ i j, i≠j → angle (z i) (z j)<lam)
    (pairB : ∀ i j, i≠j → angle (1-z i) (1-z j)<lam) :
    (∀ i, 0<(z i).re ∧ (z i).re<1) ∧
      ((∀ i, 0<(z i).im) ∨ (∀ i, (z i).im<0)) := by
  let A (i : I) := (z i).arg
  let B (i : I) := (1-z i).arg
  have en i : (1:ℂ)-z i ≠ 0 := sub_ne_zero.mpr (oneN i).symm
  have ha i : |A i|<lam := by simpa [A,one_angle (zeroN i)] using narrowA i
  have hb i : |B i|<lam := by simpa [B,one_angle (en i)] using narrowB i
  have strip (i : I) : 0<(z i).re ∧ (z i).re<1 := by
    have a := (Complex.abs_arg_lt_pi_div_two_iff.mp ((ha i).trans_le hlπ)).resolve_right (zeroN i)
    have b := (Complex.abs_arg_lt_pi_div_two_iff.mp ((hb i).trans_le hlπ)).resolve_right (en i)
    simpa using And.intro a b
  refine ⟨strip,?_⟩
  have spread {x y : ℝ} (hx : |x|<lam) (hy : |y|<lam) : -π<x-y ∧ x-y≤π := by
    obtain ⟨_,_⟩ := abs_lt.mp hx
    obtain ⟨_,_⟩ := abs_lt.mp hy
    constructor <;> linarith
  have far (i : I) : lam ≤ |A i - B i| := by
    have h := cap i
    rw [angle_neg_left,angle_in_strip (zeroN i) (en i) (spread (ha i) (hb i))] at h
    change π-|A i-B i|≤π-lam at h
    linarith
  have closeA (i j : I) (ne : i ≠ j) : |A i-A j|<lam := by
    simpa only [angle_in_strip (zeroN i) (zeroN j) (spread (ha i) (ha j)),A] using pairA i j ne
  have closeB (i j : I) (ne : i ≠ j) : |B i-B j|<lam := by
    simpa only [angle_in_strip (en i) (en j) (spread (hb i) (hb j)),B] using pairB i j ne
  have sgn (i : I) : (0<(z i).im ∧ lam≤A i-B i) ∨ ((z i).im<0 ∧ A i-B i≤ -lam) := by
    rcases lt_trichotomy (z i).im 0 with h | h | h
    · have α : A i<0 := Complex.arg_neg_iff.mpr h
      have β : 0≤B i := Complex.arg_nonneg_iff.mpr (by simpa using h.le)
      have d := far i
      rw [abs_of_nonpos (by linarith)] at d
      exact Or.inr ⟨h,by linarith⟩
    · have α : A i=0 := Complex.arg_eq_zero_iff.mpr ⟨(strip i).1.le,h⟩
      have β : B i=0 := Complex.arg_eq_zero_iff.mpr ⟨by simpa using (strip i).2.le,by simp [h]⟩
      have := far i
      simp [α,β] at this
      linarith
    · have α : 0≤A i := Complex.arg_nonneg_iff.mpr h.le
      have β : B i<0 := Complex.arg_neg_iff.mpr (by simpa using h)
      have d := far i
      rw [abs_of_nonneg (by linarith)] at d
      exact Or.inl ⟨h,d⟩
  by_cases up : ∀ i, 0<(z i).im
  · exact Or.inl up
  · push_neg at up
    obtain ⟨j,hj⟩ := up
    have q := (sgn j).resolve_left (fun h => (not_lt_of_ge hj) h.1)
    right
    intro i
    rcases sgn i with p | p
    · have ne : i ≠ j := by intro h; subst i; linarith [p.1]
      obtain ⟨_,u⟩ := abs_lt.mp (closeA i j ne)
      obtain ⟨v,_⟩ := abs_lt.mp (closeB i j ne)
      linarith [p.2,q.2]
    · exact p.1

#print axioms chart_side
end R53.TwoAnchor
