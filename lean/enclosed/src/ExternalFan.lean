import SpatialClusters
noncomputable section
namespace R53.Islands
open Real JSP404 InnerProductGeometry R51.Anchored R52.TwoAnchor

/-- A marked subset may have any shape. Every external point sees it in the indicated
angular cap about the ray to its representative. No restrictions are placed on the exterior. -/
structure Island (S F : Finset Point) (a : Point) (η : ℝ) : Prop where
  sub : F⊆S
  mem : a∈F
  pos : 0≤η
  sight : ∀ p∈S\F, InCone F p (p-a) η

theorem island_of_disk {S F : Finset Point} {a : Point} {ρ : ℝ} (sub : F⊆S) (mem : a∈F)
    (lo : 0≤ρ) (hi : ρ<1) (radius : ∀ p∈S\F, ∀ x∈F, dist a x≤ρ*dist a p) :
    Island S F a (arcsin ρ) := by
  refine ⟨sub,mem,arcsin_nonneg.mpr lo,?_⟩
  intro p hp
  exact disk_cone (fun e=> (Finset.mem_sdiff.mp hp).2 (e.symm ▸ mem)) hi (radius p hp)

theorem Island.one {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (two : 2≤F.card) {p : Point} (ext : p∈S\F) :
    (bits F+1)*defect S≤π+2*η := by
  obtain ⟨ps,pf⟩:=Finset.mem_sdiff.mp ext
  have ne : p≠a := fun e=>pf (e.symm ▸ I.mem)
  exact anchored_budget I.sub two ps pf (sub_ne_zero.mpr ne) I.pos (I.sight p ext)

/-- If the cloud requires too many binary directions, every pair of exterior rays at its
representative makes a small angle. This applies simultaneously to the entire exterior. -/
theorem Island.external_fan {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (two : 2≤F.card) (excess : π+4*η<(bits F+2)*defect S) {p q : Point}
    (hp : p∈S\F) (hq : q∈S\F) :
    EuclideanGeometry.angle p a q≤π-(bits F+1)*defect S+2*η := by
  obtain ⟨ps,pf⟩:=Finset.mem_sdiff.mp hp
  obtain ⟨qs,qf⟩:=Finset.mem_sdiff.mp hq
  by_cases eq : p=q
  · subst q
    have ne : p≠a := fun e=>pf (e.symm ▸ I.mem)
    change angle (p-a) (p-a)≤_
    rw [angle_self (sub_ne_zero.mpr ne)]
    linarith [I.one two hp]
  let A : Corner S a p q := ⟨F,I.sub,I.mem,ps,qs,pf,qf,eq,η,η,I.pos,I.pos,I.sight p hp,I.sight q hq⟩
  rcases corner A two with left|right
  · change (bits F+2)*defect S≤π+2*(η+η) at left
    linarith
  · change EuclideanGeometry.angle p a q≤π-(bits F+1)*defect S+(η+η) at right
    linarith

end R53.Islands
#print axioms R53.Islands.island_of_disk
#print axioms R53.Islands.Island.external_fan
