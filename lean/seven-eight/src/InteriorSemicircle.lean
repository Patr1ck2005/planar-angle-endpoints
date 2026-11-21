import DiameterRays

noncomputable section
namespace R91.Interior
open JSP404 Real InnerProductGeometry R54.GapTest R87.Diameter
open scoped RealInnerProductSpace

/-- Directed bearings in a full turn centered at a prescribed ray. -/
theorem full_head (v : Point) (nv : v≠0) (t : ℝ) :
    ∃a:ℝ,-π≤a ∧ a≤π ∧ Head v (t+a) := by
  obtain ⟨s,lo,hi,r,rp,e,sg,eq⟩:=lifted_polar v nv t
  rcases sg with rfl|rfl
  · refine ⟨s-t-π,by linarith,by linarith [pi_pos],r,rp,?_⟩
    have shift : circleDirection (s-π)= -circleDirection s := by
      ext k;fin_cases k <;> simp [circleDirection]
    rw [show t+(s-t-π)=s-π by ring,shift]
    simpa using eq
  · refine ⟨s-t,by linarith [pi_pos],by linarith,r,rp,?_⟩
    simpa only [add_sub_cancel,one_smul,show t+(s-t)=s by ring] using eq

/-- If two signed headings differ by at least π, their ordinary angle
is the complementary part of the full turn. -/
theorem wrap_angle {u v : Point} {t a b : ℝ} (U : Head u (t+a)) (V : Head v (t+b))
    (lo : π≤b-a) (hi : b-a≤2*π) : angle u v=2*π-(b-a) := by
  obtain ⟨r,rp,rfl⟩:=U
  obtain ⟨z,zp,rfl⟩:=V
  rw [angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ zp,angle_circleDirection,
    show t+a-(t+b)= -(b-a) by ring,cos_neg,←cos_two_pi_sub (b-a),
    arccos_cos (by linarith) (by linarith)]

/-- An origin in the true convex hull of other centers precludes a strict
open semicircle containing all their actual directed bearings. -/
theorem semicircle_span {I : Type*} {c : I→Point} (i : I)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) {t a b : ℝ}
    (heads : ∀j,j≠i→∃s,a≤s ∧ s≤b ∧ Head (c j-c i) (t+s)) : π≤b-a := by
  by_contra! small
  let mid:=t+(a+b)/2
  let u:=circleDirection mid
  have U : Head u mid:=⟨1,by norm_num,by simp [u]⟩
  let F : Point→ₗ[ℝ]ℝ:=(innerSL ℝ u).toLinearMap
  have sep : c '' {j | j≠i} ⊆ {x | F (c i)<F x} := by
    rintro _ ⟨j,hj,rfl⟩
    obtain ⟨s,sl,sb,H⟩:=heads j hj
    have half : |mid-(t+s)|<π/2:=by
      dsimp [mid];exact abs_lt.mpr ⟨by linarith,by linarith⟩
    have acute : angle u (c j-c i)<π/2:=(head_angle U H (half.le.trans (by linarith [pi_pos]))).trans_lt half
    have dot : 0<⟪u,c j-c i⟫:=lt_of_not_ge (fun le=>acute.not_ge (inner_nonpos_iff_pi_div_two_le_angle.mp le))
    change F (c i)<F (c j)
    apply sub_pos.mp
    rwa [←map_sub]
  have lin : IsLinearMap ℝ F:=⟨F.map_add,F.map_smul⟩
  have closed := convexHull_min sep (convex_halfSpace_gt lin (F (c i)))
  exact (lt_irrefl (F (c i))) (closed inside)

end R91.Interior
#print axioms R91.Interior.semicircle_span
