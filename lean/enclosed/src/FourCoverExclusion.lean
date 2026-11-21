import HighIsland
import FourIslandMargins
noncomputable section
namespace R53.FourCover
open Real JSP404 R52.FourSeparated R52.TwoAnchor R53.Islands R55.FourIslands

def aperture (k : ℕ) (e : ℝ) := min (π/4) (((k:ℝ)+3)*e/8)
def radius (sep : ℝ) (k : ℕ) (e : ℝ) := sin (aperture k e)*sep/8

theorem aperture_info (k : ℕ) {e : ℝ} (ep : 0<e) :
    0<sin (aperture k e) ∧ sin (aperture k e)<1 ∧
    arcsin (sin (aperture k e))=aperture k e ∧ 4*aperture k e<((k:ℝ)+3)*e := by
  have ap : 0<aperture k e := lt_min (by positivity) (by positivity)
  have a4 : aperture k e≤π/4 := min_le_left _ _
  have a2 : aperture k e<π/2 := by linarith [pi_pos]
  refine ⟨sin_pos_of_pos_of_lt_pi ap (by linarith [pi_pos]),?_,arcsin_sin (by linarith [pi_pos]) a2.le,?_⟩
  · simpa using Real.sin_lt_sin_of_lt_of_le_pi_div_two (show -(π/2)≤aperture k e by linarith [pi_pos])
      (le_refl (π/2)) a2
  · have val : aperture k e≤((k:ℝ)+3)*e/8 := min_le_right _ _
    linarith [mul_pos (show 0<(k:ℝ)+3 by positivity) ep]

theorem radius_pos {sep : ℝ} (sp : 0<sep) (k : ℕ) {e : ℝ} (ep : 0<e) :
    0<radius sep k e := div_pos (mul_pos (aperture_info k ep).1 sp) (by norm_num)

theorem to_island {S : Finset Point} {b D δ ρ : ℝ} (I : Islands S b D δ ρ)
    (lo : 0≤ρ) (hi : ρ<1) (i : Fin 4) : Island S (I.cell i) (I.center i) (arcsin ρ) := by
  apply island_of_disk (I.sub i) (I.middle i) lo hi
  intro p hp
  exact I.outside i p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2

theorem exterior {S : Finset Point} {b D δ ρ : ℝ} (I : Islands S b D δ ρ) (i : Fin 4) :
    (S\I.cell i).Nonempty := by
  obtain ⟨j,ne⟩:=exists_ne i
  exact ⟨I.center j,Finset.mem_sdiff.mpr ⟨I.sub j (I.middle j),Finset.disjoint_left.mp (I.disjoint j i ne) (I.middle j)⟩⟩

theorem low_excludes {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 4*2^k<S.card) {e : ℝ} (ep : 0<e)
    (ang : maxAngle S≤π-2*π/(2*(k:ℝ)+5)-e) {δ : ℝ} (dp : 0≤δ)
    (small : δ≤radius (lowSep k e) k e) : ¬DiskCover S δ (dist p q) := by
  intro cov
  obtain ⟨lo,hi,ar,lt⟩:=aperture_info k ep
  have sm : 8*δ≤sin (aperture k e)*lowSep k e := by dsimp [radius] at small;linarith
  obtain ⟨I,_,_⟩:=low_islands hp hq pq big ep ang dp lo hi.le sm cov
  obtain ⟨i,heavy⟩:=R55.FourIslands.heavy I big
  have bound:=low_stability (to_island I lo.le hi i) (exterior I i) big heavy ep.le ang
  rw [ar] at bound
  linarith

theorem high_excludes {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 5*2^k<S.card) {e : ℝ} (ep : 0<e)
    (ang : maxAngle S≤π-π/((k:ℝ)+3)-e) {δ : ℝ} (dp : 0≤δ)
    (small : δ≤radius (highSep k e) k e) : ¬DiskCover S δ (dist p q) := by
  intro cov
  obtain ⟨lo,hi,ar,lt⟩:=aperture_info k ep
  have sm : 8*δ≤sin (aperture k e)*highSep k e := by dsimp [radius] at small;linarith
  obtain ⟨I,_,_⟩:=high_islands hp hq pq big ep ang dp lo hi.le sm cov
  rcases high_heavy I big with ⟨i,h⟩|⟨i,j,_,h,h',disj⟩
  · have bound:=oversize (to_island I lo.le hi i) (exterior I i) h
    rw [ar] at bound
    let B:=(k:ℝ)+3
    have bp : 0<B := by dsimp [B];positivity
    have d : π/B+e≤defect S := by dsimp [B,defect];linarith
    have x:=mul_le_mul_of_nonneg_left d bp.le
    rw [mul_add,show B*(π/B)=π by field_simp] at x
    change B*defect S≤_ at bound
    change 4*aperture k e<B*e at lt
    linarith [show 0≤aperture k e from le_min (by positivity) (by positivity)]
  · have bound:=high_stability (to_island I lo.le hi i) (to_island I lo.le hi j) disj big h h' ang
    rw [ar] at bound
    linarith

end R53.FourCover
#print axioms R53.FourCover.low_excludes
#print axioms R53.FourCover.high_excludes
