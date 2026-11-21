import HeavyIsland
import TwoNarrowAnchors
import Jsp000404.SmallStrip
noncomputable section
namespace R53.Islands
open Real JSP404 R51.Anchored R52.TwoAnchor R53.TwoAnchor

theorem four_nonacute {S : Finset Point} (size : 4≤S.card) : defect S≤π/2 := by
  classical
  obtain ⟨Q,sub,count⟩ := Finset.exists_subset_card_eq size
  let E : Fin 4 ≃ Q := (Fintype.equivFinOfCardEq (by simpa using count)).symm
  let f (i : Fin 4) : Point := (E i).val
  have inj : Function.Injective f := fun _ _ eq=>E.injective (Subtype.ext eq)
  obtain ⟨i,j,k,ij,kj,ik,ang⟩:=Jsp404.four_points_nonacute f inj
  have bound:=angle_le_maxAngle (sub (E i).property) (sub (E j).property) (sub (E k).property)
    (inj.ne ij) (inj.ne ik) (inj.ne kj.symm)
  change _≤EuclideanGeometry.angle (E i).val (E j).val (E k).val at ang
  dsimp [defect];linarith

private theorem narrow_restriction {S F T : Finset Point} {a : Point} {η : ℝ}
    (I : Island S F a η) (two : 2≤F.card) (excess : π+4*η<(bits F+2)*defect S)
    (outside : ∀ x∈T, x≠a → x∈S\F) : Narrow T a (defect S) := by
  intro x hx y hy xa ya _
  have bound:=I.external_fan two excess (outside x hx xa) (outside y hy ya)
  linarith [I.pos]

/-- Two independently isolated large subsets and a completely arbitrary third part.
At least one of the three logarithmic cardinality budgets must hold. -/
theorem three_budgets {S F H : Finset Point} {a b : Point} {η ξ : ℝ}
    (I : Island S F a η) (J : Island S H b ξ) (disj : Disjoint F H)
    (two : 2≤F.card) (other : 2≤H.card) :
    (bits F+2)*defect S≤π+4*η ∨ (bits H+2)*defect S≤π+4*ξ ∨
    (bits (S\(F∪H))+2)*defect S≤π := by
  classical
  by_cases x : (bits F+2)*defect S≤π+4*η
  · exact Or.inl x
  by_cases y : (bits H+2)*defect S≤π+4*ξ
  · exact Or.inr (Or.inl y)
  right;right
  let W:=S\(F∪H)
  let T:=insert a (insert b W)
  have ah : a∉H := Finset.disjoint_left.mp disj I.mem
  have bf : b∉F := Finset.disjoint_left.mp disj.symm J.mem
  have ab : a≠b := fun e=>bf (e ▸ I.mem)
  have aw : a∉W := by simp [W,I.mem]
  have bw : b∉W := by simp [W,J.mem]
  have hu : F∪H⊆S := Finset.union_subset I.sub J.sub
  have card := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint disj] at card
  have cap:=four_nonacute (S:=S) (by omega)
  have dl : 0<defect S := by
    have bd : 0≤bits F+2 := by unfold bits;positivity
    by_contra! zero
    linarith [mul_nonpos_of_nonneg_of_nonpos bd zero,I.pos,pi_pos]
  have sa : a∈T := by simp [T]
  have sb : b∈T := by simp [T]
  have sub : T⊆S := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|h
    · exact I.sub I.mem
    rcases Finset.mem_insert.mp h with rfl|hw
    · exact J.sub J.mem
    exact (Finset.mem_sdiff.mp hw).1
  have na : Narrow T a (defect S) := by
    apply narrow_restriction I two (lt_of_not_ge x)
    intro z hz za
    rcases Finset.mem_insert.mp hz with e|h
    · exact (za e).elim
    rcases Finset.mem_insert.mp h with rfl|hw
    · exact Finset.mem_sdiff.mpr ⟨J.sub J.mem,bf⟩
    exact Finset.mem_sdiff.mpr ⟨sub hz,fun zf=>(Finset.mem_sdiff.mp hw).2 (Finset.mem_union_left H zf)⟩
  have nb : Narrow T b (defect S) := by
    apply narrow_restriction J other (lt_of_not_ge y)
    intro z hz zb
    rcases Finset.mem_insert.mp hz with rfl|h
    · exact Finset.mem_sdiff.mpr ⟨I.sub I.mem,ah⟩
    rcases Finset.mem_insert.mp h with e|hw
    · exact (zb e).elim
    exact Finset.mem_sdiff.mpr ⟨sub hz,fun zh=>(Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right F zh)⟩
  have lim : maxAngle T≤π-defect S := by simpa [defect] using maxAngle_mono sub
  have h:=ordinary_clog sa sb ab dl cap lim na nb
  have er : (T.erase a).erase b=W := by ext z;by_cases za : z=a <;> by_cases zb : z=b <;> simp_all [T]
  rw [er] at h
  exact h

end R53.Islands
#print axioms R53.Islands.three_budgets
