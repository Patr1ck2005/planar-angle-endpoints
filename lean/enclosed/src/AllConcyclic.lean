import ConcyclicStaircase
import TwoCircleUpper

noncomputable section
namespace R59.Concyclic
open Real JSP404 R55.WeightedCollision

/-- All finite nonsingleton common-circle collision models have exactly the
published Sendov staircase as their least attainable threshold at every N≥3. -/
theorem full_staircase {N : ℕ} (ge : 3≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  constructor
  · rcases eq_or_ne N 3 with rfl|three
    · exact equilateral
    rcases eq_or_ne N 4 with rfl|four
    · have hit:=of_two (R51.TwoCenters.sharp_by_card (N:=4) (by decide)).1
      rw [show Jsp404.alphaN 4=π-π/(2:ℕ) by norm_num [Jsp404.alphaN,Nat.clog];ring]
      simpa only [show Nat.clog 2 4=2 by decide] using hit
    have five : 5≤N := by omega
    let k:=Nat.clog 2 N-3
    have depth : 3≤Nat.clog 2 N := (by decide : 3≤Nat.clog 2 5).trans (Nat.clog_mono_right 2 five)
    have expo : k+3=Nat.clog 2 N := by dsimp [k];omega
    have lo : 4*2^k<N := by
      have h : 2^(k+2)<N := Nat.pow_lt_of_lt_clog (by omega)
      simpa [pow_add,Nat.mul_comm] using h
    have hi : N≤8*2^k := by
      have h:=Nat.le_pow_clog (by decide : 1<2) N
      rw [←expo,pow_add] at h
      simpa [Nat.mul_comm] using h
    have whole:=R53.FourCover.full_staircase ge
    by_cases cut : N≤5*2^k
    · rw [whole.unique (R53.FourCover.low_band lo cut)]
      exact low_upper lo cut
    · rw [whole.unique (R53.FourCover.high_band (lt_of_not_ge cut) hi)]
      exact high_upper ge hi
  · rintro θ ⟨k,two,c,ci,on,w,wp,total,hit⟩
    rw [←total] at ge ⊢
    exact concyclic_staircase (by simpa using two) c ci on wp ge hit

theorem spectrum {N : ℕ} (ge : 3≤N) : scores N=Set.Ici (Jsp404.alphaN N) := by
  ext θ
  exact ⟨fun h=>(full_staircase ge).2 h,fun h=>increasing (full_staircase ge).1 h⟩

/-- The remaining unrestricted assertion is precisely existence of an optimal
collision profile whose distinct macroscopic centers lie on one circle. -/
theorem unrestricted_iff {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔ alpha N∈scores N := by
  constructor
  · intro h;rw [h];exact (full_staircase ge).1
  · intro h
    exact le_antisymm (Jsp404.alpha_le_alphaN N ge) ((full_staircase ge).2 h)

#print axioms unrestricted_iff
#print axioms full_staircase
#print axioms spectrum
end R59.Concyclic

