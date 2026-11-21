import FourInteriorMass

noncomputable section
namespace R96.Endpoint
open JSP404 Real InnerProductGeometry R55.WeightedCollision

private theorem equal_radii {a b d o : Point} (ao : a≠o)
    (pa : EuclideanGeometry.angle a o d=2*π/3) (pb : EuclideanGeometry.angle b o d=2*π/3)
    (side : dist a d=dist b d) : dist a o=dist b o := by
  have val : cos (2*π/3)= -(1/2:ℝ):=by
    rw [show 2*π/3=π-π/3 by ring,cos_pi_sub,cos_pi_div_three]
  have ha:=EuclideanGeometry.law_cos a o d
  have hb:=EuclideanGeometry.law_cos b o d
  rw [pa,val,side] at ha
  rw [pb,val] at hb
  have z : (dist a o-dist b o)*(dist a o+dist b o+dist d o)=0:=by nlinarith only [ha,hb]
  have pos : 0<dist a o+dist b o+dist d o:=by
    linarith only [dist_pos.mpr ao,dist_nonneg (x:=b) (y:=o),dist_nonneg (x:=d) (y:=o)]
  exact sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right pos.ne')

/-- At total seven the three outer centers form an equilateral triangle and
the enclosed site is its circumcenter. The enumeration exhausts the other
sites and records all six ordinary angle and distance relations invariantly. -/
theorem seven_shape {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀j,0<w j) (four : Fintype.card I=4) (hit : 2*π/3∈attainable w c)
    (i : I) (inside : c i∈convexHull ℝ (c '' {a | a≠i})) (seven : (∑j,w j)=7) :
    ∃h : Fin 3↪I,(∀j,h j≠i) ∧ (∀j,j≠i→∃a,h a=j) ∧
      (∀a b,a≠b→EuclideanGeometry.angle (c (h a)) (c i) (c (h b))=2*π/3) ∧
      (∀a b d,a≠b→a≠d→b≠d→EuclideanGeometry.angle (c (h a)) (c (h b)) (c (h d))=π/3) ∧
      (∀a b d,a≠b→a≠d→b≠d→dist (c (h a)) (c (h b))=dist (c (h a)) (c (h d))) ∧
      ∀a b,dist (c (h a)) (c i)=dist (c (h b)) (c i) := by
  classical
  let : Nontrivial I:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have A:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  have mac : Macro c (π-π/3):=by rw [show π-π/3=2*π/3 by ring];exact A.2.1
  obtain ⟨h,off,near⟩:=R91.Interior.three_chords ci inside (by positivity : 0<π/3) mac
  let other:={j : I // j≠i}
  let f (a : Fin 3) : other:=⟨h a,off a⟩
  have complete : ∀j,j≠i→∃a,h a=j:=by
    have eq : Fintype.card other=3:=by simp [other,Fintype.card_subtype_compl,four]
    have onto := ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨fun _ _ e=>h.injective (congrArg Subtype.val e),by simpa using eq.symm⟩).2
    intro j ji
    obtain ⟨a,hm⟩:=onto ⟨j,ji⟩
    exact ⟨a,congrArg Subtype.val hm⟩
  let x (j : Fin 3):=c (h j)
  have central (a b : Fin 3) (ab : a≠b) : EuclideanGeometry.angle (x a) (c i) (x b)=2*π/3:=by
    have low:=(near a b ab).1
    have high:=(near a b ab).2
    dsimp [x]
    linarith
  have weights:=((four_mass ci wp four hit i inside).2.2 seven).1
  have ub (a b d : Fin 3) (ab : a≠b) (bd : b≠d) : EuclideanGeometry.angle (x a) (x b) (x d)≤π/3:=by
    obtain ⟨_,_,v,_,fan⟩:=R95.Heavy.heavy_site ci A four.ge (h b) (weights _ (off b)).ge
    have l:=fan (h a) (h.injective.ne ab)
    have r:=fan (h d) (h.injective.ne bd.symm)
    rw [angle_comm] at l
    change angle (x a-x b) (x d-x b)≤π/3
    linarith only [angle_le_angle_add_angle (x a-x b) v (x d-x b),l,r]
  have eqang (a b d : Fin 3) (ab : a≠b) (ad : a≠d) (bd : b≠d) :
      EuclideanGeometry.angle (x a) (x b) (x d)=π/3 := by
    have sum:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (x d) (ci.ne (h.injective.ne ab.symm))
    change EuclideanGeometry.angle (x a) (x b) (x d) + EuclideanGeometry.angle (x b) (x d) (x a) +
      EuclideanGeometry.angle (x d) (x a) (x b)=π at sum
    linarith only [sum,ub a b d ab bd,ub b d a bd ad.symm,ub d a b ad.symm ab]
  have sides (a b d : Fin 3) (ab : a≠b) (ad : a≠d) (bd : b≠d) : dist (x a) (x b)=dist (x a) (x d):=by
    apply EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi
    · rw [eqang a b d ab ad bd,eqang a d b ad ab bd.symm]
    · rw [eqang b a d ab.symm bd ad];linarith [pi_pos]
  refine ⟨h,off,complete,central,eqang,sides,?_⟩
  intro a b
  by_cases ab : a=b
  · rw [ab]
  obtain ⟨d,da,db⟩:=(by decide : ∀ a b : Fin 3,a≠b→∃d,d≠a ∧ d≠b) a b ab
  apply equal_radii (ci.ne (off a)) (central a d da.symm) (central b d db.symm)
  rw [dist_comm (c (h a)),dist_comm (c (h b))]
  exact sides d a b da db ab

end R96.Endpoint
#print axioms R96.Endpoint.seven_shape
