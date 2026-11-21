import ExternalFan
import Jsp000404.AcuteFanPacking
noncomputable section
namespace R53.Islands
open Real JSP404 InnerProductGeometry R51.Anchored R52.TwoAnchor

/-- Small angular diameter for the complete exterior gives a single common observing
direction for that exterior, at the marked island representative. -/
theorem reciprocal {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (two : 2≤F.card) (other : 2≤(S\F).card) :
    (bits F+2)*defect S≤π+4*η ∨ (bits F+bits (S\F)+2)*defect S≤2*π+2*η := by
  classical
  by_cases cheap : (bits F+2)*defect S≤π+4*η
  · exact Or.inl cheap
  right
  have excess:=lt_of_not_ge cheap
  let G := S\F
  let T:=π-(bits F+1)*defect S+2*η
  have ep : G.Nonempty := Finset.card_pos.mp (by change 0<(S\F).card;omega)
  obtain ⟨p,hp⟩:=ep
  have nonneg : 0≤T := by dsimp [T];linarith [I.one two hp]
  have dpos : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  have bpos : 0≤bits F := Nat.cast_nonneg _
  have short : T<π/2 := by dsimp [T];nlinarith [mul_nonneg bpos dpos]
  let o := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u (x : ↥G) : Point := a-(x:Point)
  letI : Nonempty ↥G := ⟨⟨p,hp⟩⟩
  have nz (x : ↥G) : u x≠0 := by
    apply sub_ne_zero.mpr
    intro h
    exact (Finset.mem_sdiff.mp x.property).2 (h ▸ I.mem)
  have close (x y : ↥G) : angle (u x) (u y)≤T := by
    change angle (a-(x:Point)) (a-(y:Point))≤T
    rw [←neg_sub (x:Point) a,←neg_sub (y:Point) a,angle_neg_neg]
    exact I.external_fan two excess x.property y.property
  obtain ⟨e,he,t,ht⟩:=Jsp404.exists_ray_window_of_three_mul_lt_two_pi o u nz nonneg
    (by linarith [pi_pos] : 3*T<2*π) close
  obtain ⟨v,hv,c⟩:=Jsp404.exists_inward_bisector_of_ray_window o u nz nonneg
    (by linarith [pi_pos] : T<π) e he t ht
  have cone : InCone G a v (T/2) := fun x hx=>c ⟨x,hx⟩
  have ext : a∉G := fun h=>(Finset.mem_sdiff.mp h).2 I.mem
  have result:=anchored_budget (Finset.sdiff_subset : G⊆S) other (I.sub I.mem) ext hv
    (by linarith : 0≤T/2) cone
  change (bits G+1)*defect S≤π+2*(T/2) at result
  change (bits F+bits G+2)*defect S≤_
  dsimp [T] at result
  linarith

end R53.Islands
#print axioms R53.Islands.reciprocal
