import FiveHeadings
noncomputable section
namespace R64.Five
open Real JSP404 R54.GapTest R54.ProfileFormula InnerProductGeometry

theorem actual_angle {n : ℕ} (hn : 16≤n) {i j k : Fin 5} (ij : i≠j) (ik : i≠k) :
    EuclideanGeometry.angle (point (defect n) j) (point (defect n) i) (point (defect n) k) < π-defect n := by
  let l:=defect n
  have lp:=defect_pos n
  have sm:=defect_small hn
  have nc : (16:ℝ)≤n := by exact_mod_cast hn
  have long : 16*l≤π := by nlinarith only [period n,mul_le_mul_of_nonneg_right nc lp.le,lp.le]
  have hJ:=head_bounds lp.le ij
  have hK:=head_bounds lp.le ik
  have width:= (span_bounds lp sm i).2
  unfold span at width
  have ab : |heading l i j-heading l i k| ≤(7/4)*l :=
    abs_le.mpr ⟨by linarith only [hK.2,hJ.1,width],by linarith only [hJ.2,hK.1,width]⟩
  have arc : angle (circleDirection (heading l i j)) (circleDirection (heading l i k)) =
      |heading l i j-heading l i k| := by
    rw [angle_circleDirection,←cos_abs,arccos_cos (abs_nonneg _) (by linarith only [long,lp,ab])]
  change angle (point l j-point l i) (point l k-point l i) < π-l
  rcases lt_or_gt_of_ne ij with a|a <;> rcases lt_or_gt_of_ne ik with b|b
  · obtain ⟨_,rp,h⟩:=forward a l
    obtain ⟨_,sp,t⟩:=forward b l
    rw [h,t,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,arc]
    linarith only [long,lp,ab]
  · obtain ⟨_,rp,h⟩:=forward a l
    obtain ⟨_,sp,t⟩:=backward b l
    rw [h,t,angle_neg_right,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,arc]
    linarith only [head_apart lp sm (show opposed i j k from Or.inr ⟨b,a⟩)]
  · obtain ⟨_,rp,h⟩:=backward a l
    obtain ⟨_,sp,t⟩:=forward b l
    rw [h,t,angle_neg_left,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,arc]
    linarith only [head_apart lp sm (show opposed i j k from Or.inl ⟨a,b⟩)]
  · obtain ⟨_,rp,h⟩:=backward a l
    obtain ⟨_,sp,t⟩:=backward b l
    rw [h,t,angle_neg_left,angle_neg_right,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,arc]
    linarith only [long,lp,ab]

theorem five_maxAngle {n : ℕ} (hn : 16≤n) : macroAngle (point (defect n)) < π-defect n := by
  classical
  let X:=point (defect n)
  let value (s : Fin 5×Fin 5×Fin 5) :=
    if s.1≠s.2.1 ∧ s.1≠s.2.2 ∧ s.2.1≠s.2.2 then EuclideanGeometry.angle (X s.1) (X s.2.1) (X s.2.2) else 0
  let S:=insert 0 (Finset.univ.image value)
  have nz : S.Nonempty:=⟨_,Finset.mem_insert_self _ _⟩
  have rc : (16:ℝ)≤n := by exact_mod_cast hn
  have pos : 0 < π-defect n := by
    nlinarith only [period n,mul_le_mul_of_nonneg_right rc (defect_pos n).le,defect_pos n]
  have high : S.max' nz < π-defect n := by
    rcases Finset.mem_insert.mp (S.max'_mem nz) with zero|other
    · rw [zero];exact pos
    · obtain ⟨s,_,eq⟩:=Finset.mem_image.mp other
      rw [←eq];unfold value;split
      · rename_i good
        exact actual_angle hn good.1.symm good.2.2
      · exact pos
  apply lt_of_le_of_lt _ high
  apply (macro_iff X (injective _) _).mpr
  refine ⟨S.le_max' 0 (Finset.mem_insert_self _ _),?_⟩
  intro i j k ij ik jk
  have b:=S.le_max' (value (i,j,k)) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  simpa [value,ij,ik,jk] using b

#print axioms five_maxAngle
end R64.Five