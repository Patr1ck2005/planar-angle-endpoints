import ThreeCloudBudget

noncomputable section
namespace R52.TwoAnchor
open Real JSP404 R51.Anchored InnerProductGeometry

/-- Exact angular radius of the cone from an external point to a disk,
used only as an upper bound for the actual finite cloud. -/
theorem disk_cone {F : Finset Point} {a p : Point} {ρ : ℝ} (hp : p≠a) (ratio : ρ<1)
    (small : ∀ x∈F, dist a x ≤ ρ * dist a p) : InCone F p (p-a) (arcsin ρ) := by
  intro x hx
  have dpos : 0<dist a p := dist_pos.mpr hp.symm
  have sz := small x hx
  have close : dist a x < dist a p := by nlinarith [mul_pos (sub_pos.mpr ratio) dpos]
  let θ := EuclideanGeometry.angle a p x
  have acute : θ≤π/2 := by
    by_contra! wrong
    have co := cos_nonpos_of_pi_div_two_le_of_le wrong.le
      (by dsimp [θ]; linarith [EuclideanGeometry.angle_le_pi a p x,pi_pos])
    have cs := EuclideanGeometry.law_cos a p x
    change _ = _ + _ - 2*dist a p*dist x p*cos θ at cs
    have np := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤2*dist a p*dist x p by positivity) co
    nlinarith [sq_nonneg (dist x p),mul_pos (sub_pos.mpr close) (add_pos_of_pos_of_nonneg dpos (dist_nonneg : 0≤dist a x))]
  have θ0 := EuclideanGeometry.angle_nonneg a p x
  have si := EuclideanGeometry.law_sin x p a
  rw [EuclideanGeometry.angle_comm x p a,dist_comm p a] at si
  change sin θ * dist a p = _ at si
  have ss : sin θ ≤ ρ := by
    apply (mul_le_mul_iff_left₀ dpos).mp
    calc
      sin θ * dist a p = _ := si
      _ ≤ 1 * dist a x := mul_le_mul_of_nonneg_right (sin_le_one _) dist_nonneg
      _ ≤ _ := by simpa using sz
  have appl := arcsin_le_arcsin ss
  rw [arcsin_sin (by dsimp [θ]; linarith [θ0,pi_pos]) acute] at appl
  change angle (p-a) (p-x) ≤ _
  simpa only [θ,EuclideanGeometry.angle,vsub_eq_sub,←neg_sub a p,←neg_sub x p,angle_neg_neg] using appl

/-- A finite corner specified entirely by membership and Euclidean distances. -/
structure DiskCorner (S : Finset Point) (a b c : Point) (ρ : ℝ) where
  points : Finset Point
  sub : points⊆S
  middle : a∈points
  left : b∈S
  right : c∈S
  outsideL : b∉points
  outsideR : c∉points
  ends : b≠c
  radiusL : ∀ x∈points, dist a x≤ρ*dist a b
  radiusR : ∀ x∈points, dist a x≤ρ*dist a c

def DiskCorner.corner {S : Finset Point} {a b c : Point} {ρ : ℝ} (A : DiskCorner S a b c ρ)
    (lo : 0≤ρ) (hi : ρ<1) : Corner S a b c where
  points := A.points
  sub := A.sub
  middle := A.middle
  left := A.left
  right := A.right
  outsideL := A.outsideL
  outsideR := A.outsideR
  ends := A.ends
  eL := arcsin ρ
  eR := arcsin ρ
  posL := arcsin_nonneg.mpr lo
  posR := arcsin_nonneg.mpr lo
  coneL := disk_cone (fun z => A.outsideL (z.symm ▸ A.middle)) hi A.radiusL
  coneR := disk_cone (fun z => A.outsideR (z.symm ▸ A.middle)) hi A.radiusR

theorem partition_lower {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ) {k : ℕ}
    (cover : S⊆A.points∪B.points∪C.points) (size : 4*2^k<S.card) :
    ((k:ℝ)+3)*defect S≤π+4*arcsin ρ ∨ (2*(k:ℝ)+5)*defect S≤2*π+4*arcsin ρ := by
  classical
  have total := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have ab := Finset.card_union_le A.points B.points
  exact lower_half (A.corner lo hi) (B.corner lo hi) (C.corner lo hi) ⟨le_rfl,le_rfl⟩
    ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ (by change 4*2^k<A.points.card+B.points.card+C.points.card; omega)

theorem partition_upper {S : Finset Point} {a b c : Point} {ρ : ℝ} (lo : 0≤ρ) (hi : ρ<1)
    (A : DiskCorner S a b c ρ) (B : DiskCorner S b c a ρ) (C : DiskCorner S c a b ρ) {k : ℕ}
    (cover : S⊆A.points∪B.points∪C.points) (size : 5*2^k<S.card) :
    ((k:ℝ)+3)*defect S≤π+4*arcsin ρ := by
  classical
  have total := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have ab := Finset.card_union_le A.points B.points
  exact upper_half (A.corner lo hi) (B.corner lo hi) (C.corner lo hi) ⟨le_rfl,le_rfl⟩
    ⟨le_rfl,le_rfl⟩ ⟨le_rfl,le_rfl⟩ (by change 5*2^k<A.points.card+B.points.card+C.points.card; omega)

end R52.TwoAnchor
#print axioms R52.TwoAnchor.disk_cone
#print axioms R52.TwoAnchor.partition_lower
#print axioms R52.TwoAnchor.partition_upper
