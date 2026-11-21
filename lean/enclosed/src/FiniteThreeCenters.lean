import SpatialClusters

noncomputable section
namespace R52.TwoAnchor
open Real JSP404

/-- Near the three-center limit the second arm of the lower-half bound dominates. -/
theorem thin_partition {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ) {k : ℕ}
    (cover : S⊆A.points∪B.points∪C.points) (size : 4*2^k<S.card)
    (thin : 4*((k:ℝ)+2)*arcsin ρ ≤ π) :
    (2*(k:ℝ)+5)*defect S ≤ 2*π+4*arcsin ρ := by
  rcases partition_lower lo hi A B C cover size with h|h
  · have v : 0< (k:ℝ)+3 := by positivity
    have w : 0≤2*(k:ℝ)+5 := by positivity
    apply (mul_le_mul_iff_right₀ v).mp
    nlinarith [mul_le_mul_of_nonneg_right h w]
  · exact h

/-- At the half-step angle, balanced three-cloud covers have a positive,
scale-independent lower bound on their relative disk radii. -/
theorem balanced_obstruction {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ) {k : ℕ}
    (acard : 2^k<A.points.card) (bcard : 2^k<B.points.card) (ccard : 2^k<C.points.card)
    (angle : maxAngle S≤π-2*π/(2*(k:ℝ)+5)) :
    π/(4*(2*(k:ℝ)+5)) ≤ arcsin ρ := by
  have h := balanced (A.corner lo hi) (B.corner lo hi) (C.corner lo hi)
    ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ acard bcard ccard
  change ((k:ℝ)+3)*defect S ≤ π+4*arcsin ρ at h
  have p : 0<2*(k:ℝ)+5 := by positivity
  have q : 0≤(k:ℝ)+3 := by positivity
  have l : 2*π/(2*(k:ℝ)+5)≤defect S := by dsimp [defect];linarith
  have bound := (div_le_iff₀ p).mp l
  apply (div_le_iff₀ (mul_pos (by norm_num) p)).mpr
  nlinarith [mul_le_mul_of_nonneg_right bound q,mul_le_mul_of_nonneg_right h p.le]

theorem nine {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ)
    (cover : S⊆A.points∪B.points∪C.points) (size : 9≤S.card) (thin : arcsin ρ≤π/12) :
    (5*π-4*arcsin ρ)/7 ≤ maxAngle S := by
  have z := thin_partition lo hi A B C (k:=1) cover (by norm_num;omega) (by norm_num;linarith)
  norm_num [defect] at z
  linarith

theorem seventeen {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ)
    (cover : S⊆A.points∪B.points∪C.points) (size : 17≤S.card) (thin : arcsin ρ≤π/16) :
    (7*π-4*arcsin ρ)/9 ≤ maxAngle S := by
  have z := thin_partition lo hi A B C (k:=2) cover (by norm_num;omega) (by norm_num;linarith)
  norm_num [defect] at z
  linarith

theorem twentyone {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ)
    (cover : S⊆A.points∪B.points∪C.points) (size : 21≤S.card) :
    (4*π-4*arcsin ρ)/5 ≤ maxAngle S := by
  have z := partition_upper lo hi A B C (k:=2) cover (by norm_num;omega)
  norm_num [defect] at z
  linarith

end R52.TwoAnchor
#print axioms R52.TwoAnchor.thin_partition
#print axioms R52.TwoAnchor.balanced_obstruction
#print axioms R52.TwoAnchor.nine
#print axioms R52.TwoAnchor.seventeen
#print axioms R52.TwoAnchor.twentyone
