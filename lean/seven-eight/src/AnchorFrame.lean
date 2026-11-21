import AnchorSide
import FixedAnchor

noncomputable section
namespace R53.TwoAnchor
open Real InnerProductGeometry TwoAnchorGeometry TwoAnchorCount

/-- An actual similarity expressed on the complex chart whose baseline is [0,1]. -/
theorem baseline {a b : Plane} (ab : a≠b) :
    ∃ z : Plane→ℂ, Function.Injective z ∧ z a=0 ∧ z b=1 ∧
      ∀ x y t, angle (z x-z y) (z t-z y)=angle (x-y) (t-y) := by
  let E := Complex.orthonormalBasisOneI.repr.symm
  let d := E (b-a)
  have dn : d≠0 := by
    intro e
    exact ab.symm (sub_eq_zero.mp (E.injective (by rw [map_zero]; exact e : E (b-a)=E 0)))
  let z (x : Plane) := E (x-a)/d
  have diff (x y : Plane) : z x-z y=E (x-y)/d := by
    dsimp only [z]
    rw [← sub_div,← map_sub,show (x-a)-(y-a)=x-y by abel]
  refine ⟨z,?_,by simp [z],by change d/d=1; exact div_self dn,?_⟩
  · intro x y e
    have : z x-z y=0 := sub_eq_zero.mpr e
    rw [diff,div_eq_zero_iff] at this
    have h := this.resolve_right dn
    exact sub_eq_zero.mp (E.injective (by simpa using h : E (x-y)=E 0))
  · intro x y t
    rw [diff,diff,div_eq_mul_inv,div_eq_mul_inv,angle_mul_right (inv_ne_zero dn)]
    exact E.toLinearIsometry.angle_map _ _

private theorem toPlane_one :
    Complex.orthonormalBasisOneI.repr 1=base := by rfl

/-- Once signs agree, one global choice of reflection sends every remaining
point into the open upper strip. All planar angles are preserved. -/
theorem lift_side {I : Type*} (z : I→ℂ)
    (strip : ∀ i, 0<(z i).re ∧ (z i).re<1)
    (side : (∀ i, 0<(z i).im) ∨ (∀ i, (z i).im<0)) :
    ∃ F : ℂ→Plane, Function.Injective F ∧ F 0=0 ∧ F 1=base ∧
      (∀ x y t, angle (F x-F y) (F t-F y) = angle (x-y) (t-y)) ∧
      (∀ i, 0<F (z i) 0 ∧ F (z i) 0<1) ∧ (∀ i, 0<F (z i) 1) := by
  let Q := Complex.orthonormalBasisOneI.repr
  have lift (e : ℂ ≃ₗᵢ[ℝ] ℂ) (h1 : e 1=1) (sr : ∀ i, (e (z i)).re=(z i).re)
      (sp : ∀ i, 0<(e (z i)).im) :
      ∃ F : ℂ→Plane, Function.Injective F ∧ F 0=0 ∧ F 1=base ∧
      (∀ x y t, angle (F x-F y) (F t-F y) = angle (x-y) (t-y)) ∧
      (∀ i, 0<F (z i) 0 ∧ F (z i) 0<1) ∧ (∀ i, 0<F (z i) 1) := by
    refine ⟨fun x => Q (e x),Q.injective.comp e.injective,by simp,by change Q (e 1)=base; rw [h1]; exact toPlane_one,?_,?_,?_⟩
    · intro x y t
      rw [←map_sub,←map_sub,←map_sub,←map_sub]
      exact (Q.toLinearIsometry.angle_map _ _).trans (e.toLinearIsometry.angle_map _ _)
    · intro i
      change 0<(e (z i)).re ∧ (e (z i)).re<1
      simpa only [sr] using strip i
    · exact sp
  rcases side with h | h
  · exact lift (LinearIsometryEquiv.refl ℝ ℂ) rfl (fun _ => rfl) h
  · apply lift Complex.conjLIE (by simp [Complex.conjLIE_apply]) (fun _ => rfl)
    intro i
    simpa [Complex.conjLIE_apply] using h i

#print axioms baseline
#print axioms lift_side
end R53.TwoAnchor
