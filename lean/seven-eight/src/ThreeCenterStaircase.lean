import StaircaseBands
import Jsp000404.SmallStrip

noncomputable section
namespace R52.ThreeCover
open Real JSP404 R51.TwoCenters

theorem four : IsLeast (scores 4) (π/2) := by
  classical
  constructor
  · have upper:=of_two (sharp_by_card (N:=4) (by decide)).1
    rw [show Nat.clog 2 4=2 by decide] at upper
    convert upper using 1
    ring
  · intro u hu
    apply le_of_forall_pos_le_add
    intro e ep
    obtain ⟨S,size,lim,_⟩:=hu e ep
    let E : Fin 4 ≃ S := (Fintype.equivFinOfCardEq (by simpa using size)).symm
    let p (i : Fin 4) : Point := (E i).val
    have inj : Function.Injective p := fun _ _ eq=>E.injective (Subtype.ext eq)
    obtain ⟨i,j,k,ij,kj,ik,h⟩:=Jsp404.four_points_nonacute p inj
    exact h.trans ((angle_le_maxAngle (E i).property (E j).property (E k).property
      (inj.ne ij) (inj.ne ik) (inj.ne kj.symm)).trans lim.le)

/-- The published Sendov staircase, in the notation of the pinned public statement, is
the exact minimax value on the class covered by at most three vanishing relative-radius disks. -/
theorem full_staircase {N : ℕ} (ge : 3≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  rcases eq_or_ne N 3 with rfl|three'
  · have eq : alpha 3=π/3 := le_antisymm Jsp404.alpha_upper_three (pi_div_three_le_alpha (by decide))
    simpa only [Jsp404.alphaN,←eq] using three
  rcases eq_or_ne N 4 with rfl|four'
  · have t : Jsp404.alphaN 4=π/2 := by norm_num [Jsp404.alphaN,Nat.clog];ring
    rw [t];exact four
  have five : 5≤N := by omega
  exact large_staircase five

/-- Precisely the remaining geometric assertion for the original problem: at least one
minimizing family can be covered by three disks of vanishing diameter-relative radius. -/
theorem unrestricted_iff {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔ alpha N∈scores N := by
  constructor
  · intro h;rw [h];exact (full_staircase ge).1
  · intro h
    exact le_antisymm (Jsp404.alpha_le_alphaN N ge) ((full_staircase ge).2 h)

end R52.ThreeCover
#print axioms R52.ThreeCover.low_band
#print axioms R52.ThreeCover.high_band
#print axioms R52.ThreeCover.full_staircase
#print axioms R52.ThreeCover.unrestricted_iff
