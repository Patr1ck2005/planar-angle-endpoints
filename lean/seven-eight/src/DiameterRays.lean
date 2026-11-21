import ConvexCritical

noncomputable section
namespace R87.Diameter
open JSP404 Real Finset InnerProductGeometry R54.GapTest

def Head (v : Point) (q : ℝ) := ∃r:ℝ,0<r ∧ v=r • circleDirection q

theorem Head.line {v : Point} {a : ℝ} (H : Head v a) : Bearing v a := by
  obtain ⟨r,rp,eq⟩:=H
  exact ⟨r,rp,1,Or.inr rfl,by simpa using eq⟩

theorem head_angle {u v : Point} {s t : ℝ} (U : Head u s) (V : Head v t) (span : |s-t|≤π) :
    angle u v=|s-t| := by
  obtain ⟨r,rp,rfl⟩:=U
  obtain ⟨z,zp,rfl⟩:=V
  rw [angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ zp,angle_circleDirection,
    ←cos_abs (s-t),arccos_cos (abs_nonneg _) span]

theorem head_exists {v : Point} (nv : v≠0) : ∃t,Head v t := by
  obtain ⟨t,_,_,r,rp,e,es,eq⟩:=polar v nv
  rcases es with rfl | rfl
  · refine ⟨t+π,r,rp,?_⟩
    have shift : circleDirection (t+π)= -circleDirection t := by ext k;fin_cases k <;> simp [circleDirection]
    simpa only [shift,neg_one_smul] using eq
  · exact ⟨t,r,rp,by simpa using eq⟩

/-- Actual rays in an acute half-plane can be lifted with a common sign. -/
theorem acute_head {u v : Point} {t : ℝ} (U : Head u t) (nv : v≠0) (acute : angle u v<π/2) :
    ∃a,t-π/2≤a ∧ a≤t+π/2 ∧ Head v a := by
  obtain ⟨a,lo,hi,r,rp,e,es,eq⟩:=lifted_polar v nv (t-π/2)
  have hi' : a≤t+π/2:=by linarith
  refine ⟨a,lo,hi',?_⟩
  rcases es with rfl | rfl
  · have neg : Head (-v) a := ⟨r,rp,by simp [eq]⟩
    have small : |t-a|≤π/2:=abs_le.mpr ⟨by linarith,by linarith⟩
    have lim:=head_angle U neg (small.trans (by linarith [pi_pos]))
    rw [angle_neg_right] at lim
    linarith
  · exact ⟨r,rp,by simpa using eq⟩

/-- In the diameter direction every nonzero chord at its initial point lies
strictly inside the forward half-plane. -/
theorem acute_at_diameter {p q x : Point} (px : x≠p) (bound : dist q x≤dist q p) :
    EuclideanGeometry.angle q p x<π/2 := by
  by_contra! h
  have law:=EuclideanGeometry.law_cos q p x
  have cos0:=cos_nonpos_of_pi_div_two_le_of_le h
    (by linarith [EuclideanGeometry.angle_le_pi q p x,pi_pos])
  have neg:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*dist q p*dist x p by positivity) cos0
  have ds:=mul_self_le_mul_self (dist_nonneg : 0≤dist q x) bound
  have pos:=mul_self_pos.mpr (dist_ne_zero.mpr px)
  linarith only [law,neg,ds,pos]

theorem diameter_exists {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c) :
    ∃i j,i≠j ∧ ∀a b,dist (c a) (c b)≤dist (c i) (c j) := by
  classical
  obtain ⟨⟨i,j⟩,_,maxi⟩:=exists_max_image univ (fun z : I×I=>dist (c z.1) (c z.2)) univ_nonempty
  refine ⟨i,j,?_,fun a b=>maxi (a,b) (mem_univ _)⟩
  rintro rfl
  obtain ⟨x,y,ne⟩:=exists_pair_ne I
  have h:=maxi (x,y) (mem_univ _)
  change dist (c x) (c y)≤dist (c i) (c i) at h
  rw [dist_self] at h
  exact (dist_pos.mpr (ci.ne ne)).not_ge h

end R87.Diameter
#print axioms R87.Diameter.acute_at_diameter
#print axioms R87.Diameter.acute_head
#print axioms R87.Diameter.diameter_exists
