import CommonFrameLower
import SignedFan
import Mathlib.Data.Prod.Lex
noncomputable section
namespace R67.Board
open Real JSP404 InnerProductGeometry R55.WeightedCollision
/-- Lexicographic order in y then x gives every increasing edge a positive
polar representative in the same half-open semicircle. -/
def Upper (a b : Point) : Prop := a 1<b 1 ∨ (a 1=b 1 ∧ a 0<b 0)
theorem order_points {n : ℕ} (c : Fin n→Point) (ci : Function.Injective c) :
    ∃e : Equiv.Perm (Fin n),∀i j,i<j→Upper (c (e i)) (c (e j)) := by
  classical
  let key (i : Fin n) : ℝ ×ₗ ℝ := (c i 1,c i 0)
  have inj : Function.Injective key := by
    intro i j eq
    have x:=congrArg (fun p : ℝ ×ₗ ℝ=>(ofLex p).2) eq
    have y:=congrArg (fun p : ℝ ×ₗ ℝ=>(ofLex p).1) eq
    apply ci;ext k;fin_cases k
    · exact x
    · exact y
  let S:=Finset.univ.image key
  let f (i : Fin n) : ↥S := ⟨key i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have bij : Function.Bijective f := by
    refine ⟨fun _ _ eq=>inj (congrArg Subtype.val eq),?_⟩
    rintro ⟨v,hv⟩
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    exact ⟨i,rfl⟩
  let rev:=Equiv.ofBijective f bij
  let sorted:=S.orderIsoOfFin (show S.card=n by simp [S,Finset.card_image_of_injective _ inj])
  let e:=sorted.toEquiv.trans rev.symm
  have eq (i : Fin n) : key (e i)=(sorted i).val := congrArg Subtype.val (rev.apply_symm_apply (sorted i))
  refine ⟨e,fun i j lt=>?_⟩
  have lt' : key (e i)<key (e j) := (eq i) ▸ (eq j) ▸ sorted.strictMono lt
  exact Prod.Lex.lt_iff.mp lt'

private theorem ray {x y : Point} (hi : Upper x y) :
    ∃t r : ℝ,(0≤t ∧ t<π) ∧ 0<r ∧ y-x=r • circleDirection t := by
  have yn : 0≤(y-x) 1 := by change 0≤y 1-x 1;rcases hi with h|⟨h,_⟩ <;> linarith
  have nz : y-x≠0 := sub_ne_zero.mpr (by rintro rfl;rcases hi with h|⟨_,h⟩ <;> exact (lt_irrefl _ h))
  obtain ⟨r,t,rp,lo,hi',e⟩:=exists_polar_of_second_nonneg nz yn
  refine ⟨t,r,⟨lo,lt_of_le_of_ne hi' ?_⟩,rp,e⟩
  rintro rfl
  have xeq:=congrArg (fun p : Point=>p 0) e
  have yeq:=congrArg (fun p : Point=>p 1) e
  simp [circleDirection] at xeq yeq
  rcases hi with h|⟨_,h⟩ <;> linarith

structure Chart {n : ℕ} (c : Fin n→Point) where
  u : Fin n→Fin n→ℝ
  bounded : ∀i j,i<j→0≤u i j ∧ u i j<π
  represents : ∀i j,i<j→∃r:ℝ,0<r ∧ c j-c i=r • circleDirection (u i j)

theorem sorted_chart {n : ℕ} (c : Fin n→Point) (ci : Function.Injective c) :
    ∃e : Equiv.Perm (Fin n),Nonempty (Chart (c ∘ e)) := by
  classical
  obtain ⟨e,ordered⟩:=order_points c ci
  have full (i j : Fin n) : ∃t:ℝ,i<j→(0≤t ∧ t<π) ∧ ∃r:ℝ,0<r ∧ c (e j)-c (e i)=r • circleDirection t := by
    by_cases h : i<j
    · obtain ⟨t,r,ht,hr,eq⟩:=ray (ordered i j h);exact ⟨t,fun _=>⟨ht,r,hr,eq⟩⟩
    · exact ⟨0,fun a=>(h a).elim⟩
  choose t ht using full
  exact ⟨e,⟨⟨t,fun i j lt=>(ht i j lt).1,fun i j lt=>(ht i j lt).2⟩⟩⟩

private theorem legal_pos {I : Type*} {c : I→Point} (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) {i j k : I} (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    0<EuclideanGeometry.angle (c i) (c j) (c k) := by
  apply lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _)
  intro e
  rcases EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw.mp e.symm with ⟨_,h⟩|⟨_,h⟩
  · have p:=EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr (show Sbtw ℝ (c j) (c i) (c k) from ⟨h,ci.ne ij,ci.ne ik⟩)
    linarith [mac j i k ij.symm jk ik]
  · have p:=EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr (show Sbtw ℝ (c j) (c k) (c i) from ⟨h,ci.ne jk.symm,ci.ne ik.symm⟩)
    linarith [mac j k i jk ij.symm ik.symm]

private theorem same {u v : ℝ} (hu : 0≤u ∧ u<π) (hv : 0≤v ∧ v<π) :
    angle (circleDirection u) (circleDirection v)=|u-v| := by
  simpa [R37.SignedFan.oriented] using R37.SignedFan.angle_oriented hu hv true true

theorem triangle {n : ℕ} {c : Fin n→Point} (C : Chart c) (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) {i j k : Fin n} (ij : i<j) (jk : j<k) :
    ((C.u i j<C.u i k ∧ C.u i k<C.u j k) ∨ (C.u j k<C.u i k ∧ C.u i k<C.u i j)) ∧
    π-θ≤|C.u i j-C.u j k| ∧ |C.u i j-C.u i k|≤θ ∧ |C.u i k-C.u j k|≤θ := by
  have ik:=ij.trans jk
  obtain ⟨r,rp,er⟩:=C.represents _ _ ij
  obtain ⟨s,sp,es⟩:=C.represents _ _ ik
  obtain ⟨t,tp,et⟩:=C.represents _ _ jk
  have a : EuclideanGeometry.angle (c j) (c i) (c k)=|C.u i j-C.u i k| := by
    change angle (c j-c i) (c k-c i)=_
    rw [er,es,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,same (C.bounded _ _ ij) (C.bounded _ _ ik)]
  have b : EuclideanGeometry.angle (c i) (c j) (c k)=π-|C.u i j-C.u j k| := by
    change angle (c i-c j) (c k-c j)=_
    rw [←neg_sub (c j) (c i),angle_neg_left,er,et,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ tp,same (C.bounded _ _ ij) (C.bounded _ _ jk)]
  have d : EuclideanGeometry.angle (c i) (c k) (c j)=|C.u i k-C.u j k| := by
    change angle (c i-c k) (c j-c k)=_
    rw [←neg_sub (c k) (c i),←neg_sub (c k) (c j),angle_neg_neg,es,et,angle_smul_left_of_pos _ _ sp,angle_smul_right_of_pos _ _ tp,same (C.bounded _ _ ik) (C.bounded _ _ jk)]
  have h:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c k) (ci.ne ij.ne)
  rw [EuclideanGeometry.angle_comm (c k) (c j) (c i),a,b,d] at h
  have x:=legal_pos ci lt mac ij.ne.symm jk.ne ik.ne
  have y:=legal_pos ci lt mac ik.ne ij.ne jk.ne.symm
  rw [a] at x
  rw [d] at y
  refine ⟨?_,by linarith [mac i j k ij.ne ik.ne jk.ne],by linarith [mac j i k ij.ne.symm jk.ne ik.ne],by linarith [mac i k j ik.ne ij.ne jk.ne.symm]⟩
  generalize C.u i j=A at h x y ⊢
  generalize C.u i k=B at h x y ⊢
  generalize C.u j k=D at h x y ⊢
  rcases le_total A D with l|l
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr l)] at h
    rcases le_total A B with p|p <;> rcases le_total B D with q|q <;>
      first | (rw [abs_of_nonpos (sub_nonpos.mpr p)] at h x) | (rw [abs_of_nonneg (sub_nonneg.mpr p)] at h x)
    all_goals first | (rw [abs_of_nonpos (sub_nonpos.mpr q)] at h y) | (rw [abs_of_nonneg (sub_nonneg.mpr q)] at h y)
    all_goals constructor <;> linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr l)] at h
    rcases le_total A B with p|p <;> rcases le_total B D with q|q <;>
      first | (rw [abs_of_nonpos (sub_nonpos.mpr p)] at h x) | (rw [abs_of_nonneg (sub_nonneg.mpr p)] at h x)
    all_goals first | (rw [abs_of_nonpos (sub_nonpos.mpr q)] at h y) | (rw [abs_of_nonneg (sub_nonneg.mpr q)] at h y)
    all_goals constructor <;> linarith
#print axioms sorted_chart
#print axioms triangle
end R67.Board
