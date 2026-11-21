import ThreeCenterStaircase
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace R52.ThreeCover
open Filter Topology JSP404 Real

theorem Covered.mono {S : Finset Point} {δ η : ℝ} (h : Covered S δ) (le : δ≤η) : Covered S η := by
  obtain ⟨p,hp,q,hq,pq,c,cover⟩:=h
  refine ⟨p,hp,q,hq,pq,c,?_⟩
  intro x hx
  obtain ⟨i,hi⟩:=cover x hx
  exact ⟨i,hi.trans (mul_le_mul_of_nonneg_right le dist_nonneg)⟩

/-- The precise residual problem in sequence language, including convergence of ordinary
finite maximum angles to the unrestricted infimum. -/
theorem unrestricted_iff_minimizing_sequence {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔ ∃ S : ℕ→Finset Point,
      (∀ m,(S m).card=N) ∧
      Tendsto (fun m=>maxAngle (S m)) atTop (𝓝 (alpha N)) ∧
      ∀ m,Covered (S m) (1/((m:ℝ)+1)) := by
  rw [unrestricted_iff ge]
  let e (m : ℕ) : ℝ:=1/((m:ℝ)+1)
  have pos (m : ℕ) : 0<e m := by dsimp [e];positivity
  have zero : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · intro h
    choose S size cap cover using fun m=>h (e m) (pos m)
    refine ⟨S,size,?_,cover⟩
    have upper : Tendsto (fun m=>alpha N+e m) atTop (𝓝 (alpha N)) := by
      simpa using (tendsto_const_nhds (x:=alpha N)).add zero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper
      (fun m=>alpha_le_maxAngle ge (size m)) (fun m=>(cap m).le)
  · rintro ⟨S,size,lim,cover⟩ δ dp
    have small : ∀ᶠ m in atTop,e m<δ := zero.eventually_lt tendsto_const_nhds dp
    have near : ∀ᶠ m in atTop,maxAngle (S m)<alpha N+δ :=
      lim.eventually_lt tendsto_const_nhds (lt_add_of_pos_right _ dp)
    obtain ⟨m,em,ang⟩:=(small.and near).exists
    exact ⟨S m,size m,ang,(cover m).mono em.le⟩

end R52.ThreeCover
#print axioms R52.ThreeCover.unrestricted_iff_minimizing_sequence
