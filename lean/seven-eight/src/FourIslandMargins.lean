import FourIslands
noncomputable section
namespace R55.FourIslands
open Real JSP404 R52.FourSeparated

/-- The R52 data use a for the third and c*a for the fourth separation,
both measured relative to the original chosen baseline. -/
theorem from_four {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {a c δ ρ : ℝ} (ap : 0<a) (a1 : a≤1) (cp : 0<c) (c1 : c≤1)
    (four : Four S p q (a*dist p q) (c*(a*dist p q))) (ep : 0≤δ) (rp : 0<ρ) (r1 : ρ≤1)
    (small : 8*δ≤ρ*(c*a)) (cover : DiskCover S δ (dist p q)) :
    ∃ I : Islands S (c*a) (dist p q) δ ρ, I.center 0=p ∧ I.center 1=q := by
  have dp:=dist_pos.mpr pq
  have ca : c*a≤a := by simpa using mul_le_mul_of_nonneg_right c1 ap.le
  obtain ⟨v,v0,v1,mem,sep⟩:=representatives hp hq four
    (a:=(c*a)*dist p q) (by simpa using mul_le_mul_of_nonneg_right (ca.trans a1) dp.le)
    (mul_le_mul_of_nonneg_right ca dp.le) (by rw [mul_assoc])
  obtain ⟨balls,cov⟩:=cover
  obtain ⟨I,_,eq,_⟩:=partition dp (mul_pos cp ap) ep rp r1 small v mem sep balls cov
  exact ⟨I,eq ▸ v0,eq ▸ v1⟩

def lowSep (k : ℕ) (ε : ℝ) := sin (lowEta k ε)*sin (lowPhi k)
def highSep (k : ℕ) (ε : ℝ) := sin (highEta k ε)*sin (highPhi k ε)

theorem lowSep_pos (k : ℕ) {ε : ℝ} (ep : 0<ε) : 0<lowSep k ε := by
  obtain ⟨p0,p1,e0,e1⟩:=lower_separation k ep
  exact mul_pos (sin_pos_of_pos_of_lt_pi e0 (by linarith [pi_pos])) (sin_pos_of_pos_of_lt_pi p0 p1)

theorem highSep_pos (k : ℕ) {ε : ℝ} (ep : 0<ε) : 0<highSep k ε := by
  obtain ⟨p0,p1,e0,e1⟩:=upper_separation k ep
  exact mul_pos (sin_pos_of_pos_of_lt_pi e0 (by linarith [pi_pos])) (sin_pos_of_pos_of_lt_pi p0 p1)

theorem low_islands {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 4*2^k<S.card) {ε : ℝ} (ep : 0<ε)
    (ang : maxAngle S≤π-2*π/(2*(k:ℝ)+5)-ε)
    {δ ρ : ℝ} (dp : 0≤δ) (rp : 0<ρ) (r1 : ρ≤1) (small : 8*δ≤ρ*lowSep k ε)
    (cover : DiskCover S δ (dist p q)) :
    ∃ I : Islands S (lowSep k ε) (dist p q) δ ρ, I.center 0=p ∧ I.center 1=q := by
  obtain ⟨p0,p1,e0,e1⟩:=lower_separation k ep
  exact from_four hp hq pq (sin_pos_of_pos_of_lt_pi p0 p1) (sin_le_one _)
    (sin_pos_of_pos_of_lt_pi e0 (by linarith [pi_pos])) (sin_le_one _)
    (low_margin hp hq pq big ep ang) dp rp r1 small cover

theorem high_islands {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 5*2^k<S.card) {ε : ℝ} (ep : 0<ε)
    (ang : maxAngle S≤π-π/((k:ℝ)+3)-ε)
    {δ ρ : ℝ} (dp : 0≤δ) (rp : 0<ρ) (r1 : ρ≤1) (small : 8*δ≤ρ*highSep k ε)
    (cover : DiskCover S δ (dist p q)) :
    ∃ I : Islands S (highSep k ε) (dist p q) δ ρ, I.center 0=p ∧ I.center 1=q := by
  obtain ⟨p0,p1,e0,e1⟩:=upper_separation k ep
  exact from_four hp hq pq (sin_pos_of_pos_of_lt_pi p0 p1) (sin_le_one _)
    (sin_pos_of_pos_of_lt_pi e0 (by linarith [pi_pos])) (sin_le_one _)
    (high_margin hp hq pq big ep ang) dp rp r1 small cover

theorem choose_radius {b ρ t : ℝ} (bp : 0<b) (rp : 0<ρ) (tp : 0<t) :
    ∃ δ : ℝ, 0<δ ∧ δ<t ∧ 8*δ≤ρ*b := by
  refine ⟨min (t/2) (ρ*b/8),lt_min (by positivity) (by positivity),?_,?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · linarith [min_le_right (t/2) (ρ*b/8)]

/-- The radius is chosen before the configuration, the moving disks and the
baseline. The output includes an actual heavy cell. -/
theorem low_small (k : ℕ) {ε ρ t : ℝ} (ep : 0<ε) (rp : 0<ρ) (r1 : ρ≤1) (tp : 0<t) :
    ∃ δ : ℝ, 0<δ ∧ δ<t ∧ ∀ {S : Finset Point} {p q : Point}, p∈S → q∈S → p≠q →
      4*2^k<S.card → maxAngle S≤π-2*π/(2*(k:ℝ)+5)-ε → DiskCover S δ (dist p q) →
      ∃ I : Islands S (lowSep k ε) (dist p q) δ ρ,
        I.center 0=p ∧ I.center 1=q ∧ ∃ i,2^k<(I.cell i).card := by
  obtain ⟨δ,dp,dt,small⟩:=choose_radius (lowSep_pos k ep) rp tp
  refine ⟨δ,dp,dt,?_⟩
  intro S p q ps qs pq size ang cover
  obtain ⟨I,i0,i1⟩:=low_islands ps qs pq size ep ang dp.le rp r1 small cover
  exact ⟨I,i0,i1,heavy I size⟩

theorem high_small (k : ℕ) {ε ρ t : ℝ} (ep : 0<ε) (rp : 0<ρ) (r1 : ρ≤1) (tp : 0<t) :
    ∃ δ : ℝ, 0<δ ∧ δ<t ∧ ∀ {S : Finset Point} {p q : Point}, p∈S → q∈S → p≠q →
      5*2^k<S.card → maxAngle S≤π-π/((k:ℝ)+3)-ε → DiskCover S δ (dist p q) →
      ∃ I : Islands S (highSep k ε) (dist p q) δ ρ, I.center 0=p ∧ I.center 1=q ∧
        ((∃ i,2*2^k<(I.cell i).card) ∨ ∃ i j,i≠j ∧ 2^k<(I.cell i).card ∧ 2^k<(I.cell j).card ∧
            Disjoint (I.cell i) (I.cell j)) := by
  obtain ⟨δ,dp,dt,small⟩:=choose_radius (highSep_pos k ep) rp tp
  refine ⟨δ,dp,dt,?_⟩
  intro S p q ps qs pq size ang cover
  obtain ⟨I,i0,i1⟩:=high_islands ps qs pq size ep ang dp.le rp r1 small cover
  exact ⟨I,i0,i1,high_heavy I size⟩

end R55.FourIslands
#print axioms R55.FourIslands.from_four
#print axioms R55.FourIslands.low_small
#print axioms R55.FourIslands.high_small
