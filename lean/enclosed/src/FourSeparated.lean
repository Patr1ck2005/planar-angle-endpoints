import MetricObstruction
import FiniteThreeCenters
noncomputable section
namespace R52.FourSeparated
open Real JSP404 R52.TwoAnchor R51.Metric

/-- A third point is separated from the given baseline pair by σ, and a fourth from all three by τ. -/
def Four (S : Finset Point) (p q : Point) (σ τ : ℝ) := ∃ x∈S,
    σ≤dist x p ∧ σ≤dist x q ∧ ∃ y∈S, τ<dist y p ∧ τ<dist y q ∧ τ<dist y x

private def cell (S : Finset Point) (a : Point) (R : ℝ) := S.filter (fun x=>dist x a≤R)

private def corner {S : Finset Point} {a b c : Point} (ha : a∈S) (hb : b∈S) (hc : c∈S) (bc : b≠c)
    {l ρ : ℝ} (lp : 0<l) (ab : l≤dist a b) (ac : l≤dist a c) (lo : 0≤ρ) (hi : ρ<1) :
    DiskCorner S a b c ρ where
  points := cell S a (ρ*l)
  sub := Finset.filter_subset _ _
  middle := Finset.mem_filter.mpr ⟨ha,by simpa using mul_nonneg lo lp.le⟩
  left := hb
  right := hc
  outsideL := by
    intro h
    have hit:dist b a≤ρ*l := (Finset.mem_filter.mp h).2
    rw [dist_comm] at hit
    linarith [mul_lt_mul_of_pos_right hi lp]
  outsideR := by
    intro h
    have hit:dist c a≤ρ*l := (Finset.mem_filter.mp h).2
    rw [dist_comm] at hit
    linarith [mul_lt_mul_of_pos_right hi lp]
  ends := bc
  radiusL := by
    intro x hx
    have h:dist x a≤ρ*l := (Finset.mem_filter.mp hx).2
    rw [dist_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left ab lo)
  radiusR := by
    intro x hx
    have h:dist x a≤ρ*l := (Finset.mem_filter.mp hx).2
    rw [dist_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left ac lo)

/-- If the three disks of radius ρl fail to cover S, there is an actual fourth point.
Any contradiction for the disk-covered case therefore implies a metric packing bound. -/
private theorem fourth {S : Finset Point} {p q x : Point} (hp : p∈S) (hq : q∈S) (hx : x∈S)
    {l ρ : ℝ} (lp : 0<l) (pq : l≤dist p q) (xp : l≤dist x p) (xq : l≤dist x q)
    (lo : 0≤ρ) (hi : ρ<1)
    (reject : ∀ (A : DiskCorner S p q x ρ) (B : DiskCorner S q x p ρ)
      (C : DiskCorner S x p q ρ), S⊆A.points∪B.points∪C.points → False) : Four S p q l (ρ*l) := by
  classical
  have pq' : p≠q := dist_pos.mp (lp.trans_le pq)
  have xp' : x≠p := dist_pos.mp (lp.trans_le xp)
  have xq' : x≠q := dist_pos.mp (lp.trans_le xq)
  let A:=corner hp hq hx xq'.symm lp pq (dist_comm p x ▸ xp) lo hi
  let B:=corner hq hx hp xp' lp (dist_comm q x ▸ xq) (dist_comm q p ▸ pq) lo hi
  let C:=corner hx hp hq pq' lp xp xq lo hi
  refine ⟨x,hx,xp,xq,?_⟩
  by_contra! no
  apply reject A B C
  intro y hy
  change y∈cell S p (ρ*l)∪cell S q (ρ*l)∪cell S x (ρ*l)
  by_cases yp : dist y p≤ρ*l
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy,yp⟩))
  by_cases yq : dist y q≤ρ*l
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy,yq⟩))
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy,no y hy (lt_of_not_ge yp) (lt_of_not_ge yq)⟩)

private theorem start {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (large : 4*2^k<S.card) {φ ρ : ℝ} (ph : 0<φ) (ph' : φ<π) (lo : 0≤ρ) (hi : ρ<1)
    (budget : π+2*φ≤((k:ℝ)+3)*defect S)
    (reject : ∀ x∈S, ∀ (A : DiskCorner S p q x ρ) (B : DiskCorner S q x p ρ)
      (C : DiskCorner S x p q ρ), S⊆A.points∪B.points∪C.points → False) :
    Four S p q (sin φ*dist p q) (ρ*(sin φ*dist p q)) := by
  have sz : 2^((k+1)+1)<S.card := by simpa [pow_succ] using (show 2^k*2*2<S.card by omega)
  have h : π+2*φ≤(((k+1:ℕ):ℝ)+2)*(π-maxAngle S) := by
    simpa only [Nat.cast_add,Nat.cast_one,defect,show (k:ℝ)+1+2=(k:ℝ)+3 by ring] using budget
  obtain ⟨x,hx,xp,xq⟩:=separated_third hp hq pq sz ph h
  exact fourth hp hq hx (mul_pos (sin_pos_of_pos_of_lt_pi ph ph') (dist_pos.mpr pq))
    (by simpa using mul_le_mul_of_nonneg_right (sin_le_one φ) (dist_nonneg : 0≤dist p q))
    xp xq lo hi (reject x hx)

/-- Low half-step. Every strict competitor contains four quantitatively separated actual points.
The baseline may be any pair, in particular a diameter. -/
theorem lower_half_four {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (size : 4*2^k<S.card) {φ ρ : ℝ} (ph : 0<φ) (ph' : φ<π) (lo : 0≤ρ) (hi : ρ<1)
    (third : π+2*φ≤((k:ℝ)+3)*defect S)
    (first : π+4*arcsin ρ<((k:ℝ)+3)*defect S)
    (second : 2*π+4*arcsin ρ<(2*(k:ℝ)+5)*defect S) :
    Four S p q (sin φ*dist p q) (ρ*(sin φ*dist p q)) := by
  apply start hp hq pq size ph ph' lo hi third
  intro x hx A B C cover
  rcases partition_lower lo hi A B C cover size with h|h <;> linarith

/-- Upper half-step. The single defect slack supplies the third and the fourth separation. -/
theorem upper_half_four {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (size : 5*2^k<S.card) {φ ρ : ℝ} (ph : 0<φ) (ph' : φ<π) (lo : 0≤ρ) (hi : ρ<1)
    (third : π+2*φ≤((k:ℝ)+3)*defect S) (fourth : π+4*arcsin ρ<((k:ℝ)+3)*defect S) :
    Four S p q (sin φ*dist p q) (ρ*(sin φ*dist p q)) := by
  apply start hp hq pq (k:=k) (by omega) ph ph' lo hi third
  intro x hx A B C cover
  have h:=partition_upper lo hi A B C cover size
  linarith

end R52.FourSeparated
#print axioms R52.FourSeparated.lower_half_four
#print axioms R52.FourSeparated.upper_half_four
