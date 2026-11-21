import HighIsland
import SendovScores
noncomputable section
namespace R53.Mass
open Real JSP404 R53.Islands R52.SendovCloud

/-- A large isolated part with positive exterior. Only its angular size is prescribed. -/
def Large (S : Finset Point) (m : ℕ) (η : ℝ) := ∃ F : Finset Point, ∃ a : Point,
  Island S F a η ∧ (S\F).Nonempty ∧ m<F.card
def Pair (S : Finset Point) (m : ℕ) (η : ℝ) := ∃ F H : Finset Point, ∃ a b : Point,
  Island S F a η ∧ Island S H b η ∧ Disjoint F H ∧ m<F.card ∧ m<H.card
def scores (N : ℕ) (property : Finset Point→ℝ→Prop) : Set ℝ := {u | ∀ η : ℝ,0<η →
  ∃ S : Finset Point,S.card=N ∧ maxAngle S<u+η ∧ property S η}

def lowClass (k : ℕ) (S : Finset Point) (η : ℝ) := Large S (2^k) η
def highClass (k : ℕ) (S : Finset Point) (η : ℝ) := Large S (2*2^k) η ∨ Pair S (2^k) η

theorem loosen {S F : Finset Point} {a : Point} {η ξ : ℝ} (I : Island S F a η) (le : η≤ξ) :
    Island S F a ξ := ⟨I.sub,I.mem,I.pos.trans le,fun p hp x hx=>(I.sight p hp x hx).trans le⟩

theorem sendov_piece {k N : ℕ} {e r : ℝ} (F : FiniteCloud k N e r) {v : ℝ}
    (vp : 0<v) (v1 : v<1) (small : r≤v/2) (i : Fin 3) :
    Island F.points (F.piece i) (center k i) (arcsin v) := by
  apply island_of_disk (fun x hx=>(F.partition x).mpr ⟨i,hx⟩) (F.centers i) vp.le v1
  intro p hp x hx
  obtain ⟨ps,pf⟩:=Finset.mem_sdiff.mp hp
  obtain ⟨j,pj⟩:=(F.partition p).mp ps
  have ne : i≠j := fun h=>pf (h ▸ pj)
  let D:=dist (center k i) (center k j)
  have d0 : 0≤D := dist_nonneg
  have one : dist (center k i) x≤v/2*D := (F.radius i j ne x hx).le.trans (mul_le_mul_of_nonneg_right small d0)
  have other:=F.radius j i ne.symm p pj
  rw [dist_comm (center k j) (center k i)] at other
  have sh : r≤1/2 := by linarith
  have bound:dist (center k j) p≤1/2*D := other.le.trans (mul_le_mul_of_nonneg_right sh d0)
  have tri:=dist_triangle (center k i) p (center k j)
  rw [dist_comm p (center k j)] at tri
  change D≤_ at tri
  have gap : D/2≤dist (center k i) p := by linarith
  nlinarith [mul_le_mul_of_nonneg_left gap vp.le]

theorem low_witness {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    π-2*π/(2*(k:ℝ)+5)∈scores N (lowClass k) := by
  classical
  intro e ep
  let t:=min (π/4) e
  have tp : 0<t := lt_min (by positivity) ep
  have small : t<π/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith [pi_pos])
  let v:=sin t
  have vp : 0<v := sin_pos_of_pos_of_lt_pi tp (by linarith [pi_pos])
  have v1 : v<1 := by simpa [v] using Real.sin_lt_sin_of_lt_of_le_pi_div_two (show -(π/2)≤t by linarith [pi_pos]) (le_refl (π/2)) small
  have asin : arcsin v≤e := by rw [show arcsin v=t from arcsin_sin (by linarith [pi_pos]) small.le];exact min_le_right _ _
  have power:=Nat.one_le_pow k 2 (by decide)
  obtain ⟨F⟩:=finite_clouds (k:=k) (N:=N) (by omega) hi ep (show 0<v/2 by positivity)
  have all : F.points=Finset.univ.biUnion F.piece := by ext x;simp [F.partition]
  have card:=Finset.card_biUnion_le (s:=(Finset.univ : Finset (Fin 3))) (t:=F.piece)
  rw [←all,F.card] at card
  have exists_big : ∃ i,2^k<(F.piece i).card := by
    by_contra! no
    have bound:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>no i)
    simp at bound
    omega
  obtain ⟨i,big⟩:=exists_big
  obtain ⟨j,ne⟩:=exists_ne i
  have sub (u : Fin 3) := (F.partition _).mpr ⟨u,F.centers u⟩
  have out : (F.points\F.piece i).Nonempty := ⟨center k j,Finset.mem_sdiff.mpr ⟨sub j,Finset.disjoint_left.mp (F.disjoint j i ne) (F.centers j)⟩⟩
  exact ⟨F.points,F.card,(cap_source k) ▸ F.angle,F.piece i,center k i,
    loosen (sendov_piece F vp v1 (le_refl _) i) asin,out,big⟩

end R53.Mass
#print axioms R53.Mass.low_witness
