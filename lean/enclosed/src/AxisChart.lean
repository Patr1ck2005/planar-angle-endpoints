import JSP404.ThreeClusterGeometry
noncomputable section
namespace R54.GapTest
open Real JSP404 InnerProductGeometry
/-- The actual nonzero vector lies on the projective line of direction a. -/
def Bearing (x:Point) (a:ℝ) : Prop :=
  ∃z:ℝ,0<z ∧ ∃e:ℝ,(e= -1 ∨ e=1) ∧ x=z • (e • circleDirection a)

theorem polar (x:Point) (nz:x≠0) : ∃a:ℝ,0≤a ∧ a≤π ∧ Bearing x a := by
  by_cases up:0≤x 1
  · obtain ⟨r,a,rp,lo,hi,eq⟩:=exists_polar_of_second_nonneg nz up
    exact ⟨a,lo,hi,r,rp,1,Or.inr rfl,by simpa using eq⟩
  · have pos:0≤(-x) 1:=by change 0≤ -(x 1);linarith
    obtain ⟨r,a,rp,lo,hi,eq⟩:=exists_polar_of_second_nonneg (neg_ne_zero.mpr nz) pos
    exact ⟨a,lo,hi,r,rp,-1,Or.inl rfl,by simpa using congrArg Neg.neg eq⟩

private def turn (a:ℝ) (x:Point) : Point :=
  !₂[cos a*x 0-sin a*x 1,sin a*x 0+cos a*x 1]

private theorem undo (t:ℝ) (x:Point) : turn t (turn (-t) x)=x := by
  ext k
  fin_cases k <;> simp [turn] <;> nlinarith [cos_sq_add_sin_sq t,
    congrArg (fun z:ℝ=>z*x 0) (cos_sq_add_sin_sq t),
    congrArg (fun z:ℝ=>z*x 1) (cos_sq_add_sin_sq t)]

private theorem turn_bearing (t a:ℝ) (x:Point) (line:Bearing x a) : Bearing (turn t x) (t+a) := by
  obtain ⟨r,rp,e,es,rfl⟩:=line
  refine ⟨r,rp,e,es,?_⟩
  ext k
  fin_cases k <;> simp [turn,circleDirection,cos_add,sin_add] <;> ring

theorem lifted_polar (x:Point) (nz:x≠0) (t:ℝ) :
    ∃a:ℝ,t≤a ∧ a≤t+π ∧ Bearing x a := by
  have nn:turn (-t) x≠0:=by
    intro e
    have bad:=undo t x
    rw [e] at bad
    apply nz
    rw [←bad]
    ext k;fin_cases k <;> simp [turn]
  obtain ⟨a,lo,hi,line⟩:=polar _ nn
  exact ⟨t+a,by linarith,by linarith,by simpa only [undo] using turn_bearing t a _ line⟩

theorem bearing_closes {x:Point} {a:ℝ} (line:Bearing x a) : Bearing x (a+π) := by
  obtain ⟨r,rp,e,es,eq⟩:=line
  have sh:circleDirection (a+π)= -circleDirection a:=by ext k;fin_cases k <;> simp [circleDirection]
  refine ⟨r,rp,-e,by rcases es with rfl|rfl <;> simp,by rw [sh];simpa using eq⟩

theorem apart {x y:Point} {a b δ:ℝ} (X:Bearing x a) (Y:Bearing y b)
    (span:|a-b|≤π) (limit:∀r:ℝ,(r= -1 ∨ r=1)→angle (r • x) y≤π-δ) : δ≤|a-b| := by
  have h1:=limit 1 (Or.inr rfl)
  have h2:=limit (-1) (Or.inl rfl)
  obtain ⟨z,zp,e,es,rfl⟩:=X
  obtain ⟨v,vp,f,fs,rfl⟩:=Y
  have exactAngle:angle (circleDirection a) (circleDirection b)=|a-b|:=by
    rw [angle_circleDirection,←cos_abs (a-b),arccos_cos (abs_nonneg _) span]
  rcases es with rfl|rfl <;> rcases fs with rfl|rfl <;>
    simp only [one_smul,neg_one_smul,angle_neg_left,angle_smul_left_of_pos _ _ zp,
      angle_smul_right_of_pos _ _ vp,angle_neg_right,exactAngle] at h1 h2 <;> linarith

#print axioms lifted_polar
#print axioms apart
end R54.GapTest
