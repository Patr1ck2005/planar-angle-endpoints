import EnclosedAngle
import SharpInteriorAxes
import InteriorMacro

noncomputable section
namespace R89.Sharp
open Real JSP404 R55.WeightedCollision

/-- Attainable maximum angles over all finite supports carrying a specified
positive weight W at a site enclosed by the rest. All other weights are free. -/
def enclosedCaps (W : ℕ) : Set ℝ := {θ | ∃ m : ℕ,∃ c : Fin (m+2)→Point,
  Function.Injective c ∧ ∃w : Fin (m+2)→ℕ,(∀j,0<w j) ∧ ∃i,w i=W ∧
  c i∈convexHull ℝ (c '' {j | j≠i}) ∧ θ∈attainable w c}

def criticalAngle (W : ℕ) : ℝ := π-π/((Nat.clog 2 W:ℝ)+3)

theorem four_site_equality {W : ℕ} (wp : 0<W) :
    ∃c : Fin 4→Point,Function.Injective c ∧ c 0∈convexHull ℝ (c '' {j | j≠0}) ∧
      criticalAngle W∈attainable (weights W) c := by
  let d:ℝ:=(Nat.clog 2 W:ℝ)+3
  let δ:=π/d
  have den : 0<d:=by dsimp [d];positivity
  have dp : 0<δ:=div_pos pi_pos den
  have per : d*δ=π:=by dsimp [δ];field_simp
  have small : δ≤π/3:=by
    have dm : (3:ℝ)≤d:=by dsimp [d];linarith [Nat.cast_nonneg (Nat.clog 2 W) (α:=ℝ)]
    have h:=mul_le_mul_of_nonneg_right dm dp.le
    linarith only [h,per]
  let c:=R90.Interior.c δ
  obtain ⟨ci,inside,mac⟩:=R90.Interior.configuration dp small
  have covers : ({c 1,c 2,c 3}:Set Point) ⊆ c '' {j | j≠0} := by
    intro p mem
    rcases mem with rfl|mem
    · exact ⟨1,by decide,rfl⟩
    rcases mem with rfl|mem
    · exact ⟨2,by decide,rfl⟩
    obtain rfl : p=c 3:=mem
    exact ⟨3,by decide,rfl⟩
  refine ⟨c,ci,convexHull_mono covers inside,?_⟩
  exact interior_axes wp dp per (by rfl) (by rfl) (by rfl) (by rfl) ci mac

/-- Sharp for every positive integer W, with equality realized on exactly four
distinct centers and unit weights at the three surrounding sites. -/
theorem sharp {W : ℕ} (wp : 0<W) : IsLeast (enclosedCaps W) (criticalAngle W) := by
  constructor
  · obtain ⟨c,ci,inside,hit⟩:=four_site_equality wp
    exact ⟨2,c,ci,weights W,weights_pos wp,0,by simp [weights],inside,hit⟩
  · rintro θ ⟨m,c,ci,w,pos,i,size,inside,hit⟩
    have h:=R89.Interior.enclosed_angle ci pos hit i inside
    simpa only [criticalAngle,←size] using h

/-- An enclosed cluster of five points forces 150 degrees even if its other
centers and all other multiplicities may be chosen freely. -/
theorem five : IsLeast (enclosedCaps 5) (5*π/6) := by
  have h:=sharp (W:=5) (by decide)
  rw [criticalAngle,show Nat.clog 2 5=3 by decide] at h
  convert h using 1
  norm_num
  ring
end R89.Sharp
#print axioms R89.Sharp.four_site_equality
#print axioms R89.Sharp.sharp
#print axioms R89.Sharp.five
