import FourCoverBoundary
noncomputable section
namespace R53.FourCover
open Real JSP404 Filter Topology

theorem full_staircase {N : ℕ} (ge : 3≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  have three:=R52.ThreeCover.full_staircase ge
  have transfer (t : ℝ) (x : IsLeast (R52.ThreeCover.scores N) t) (y : IsLeast (scores N) t) :
      IsLeast (scores N) (Jsp404.alphaN N) := (x.unique three) ▸ y
  rcases eq_or_ne N 3 with rfl|ne3
  · refine ⟨from_three three.1,?_⟩
    intro u hu
    change π/3≤u
    apply le_of_forall_pos_le_add
    intro e ep
    obtain ⟨S,sz,lim,_⟩:=hu e ep
    exact (pi_div_three_le_alpha (by decide : 3≤3)).trans ((alpha_le_maxAngle (by decide) sz).trans lim.le)
  rcases eq_or_ne N 4 with rfl|ne4
  · refine ⟨from_three three.1,?_⟩
    intro u hu
    rw [show Jsp404.alphaN 4=π/2 by norm_num [Jsp404.alphaN,Nat.clog];ring]
    apply le_of_forall_pos_le_add
    intro e ep
    obtain ⟨S,sz,lim,_⟩:=hu e ep
    have h:=R53.Islands.four_nonacute (S:=S) (by omega)
    unfold R52.TwoAnchor.defect at h
    linarith
  have five : 5≤N := by omega
  let k:=Nat.clog 2 N-3
  have log : 3≤Nat.clog 2 N := (by decide : 3≤Nat.clog 2 5).trans (Nat.clog_mono_right 2 five)
  have exp : k+3=Nat.clog 2 N := by dsimp [k];omega
  have low : 4*2^k<N := by
    have h : 2^(k+2)<N := Nat.pow_lt_of_lt_clog (by omega)
    simpa [pow_add,Nat.mul_comm] using h
  have high : N≤8*2^k := by
    have h:=Nat.le_pow_clog (by decide : 1<2) N
    rw [←exp,pow_add] at h
    simpa [Nat.mul_comm] using h
  by_cases cut : N≤5*2^k
  · exact transfer _ (R52.ThreeCover.low_band low cut) (low_band low cut)
  · exact transfer _ (R52.ThreeCover.high_band (lt_of_not_ge cut) high) (high_band (lt_of_not_ge cut) high)

theorem equal_scores {N : ℕ} (ge : 3≤N) : scores N=R52.ThreeCover.scores N := by
  ext u
  exact ⟨fun hu=>R52.ThreeCover.monotone (R52.ThreeCover.full_staircase ge).1
    ((full_staircase ge).2 hu),from_three⟩

theorem unrestricted_iff {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔ alpha N∈scores N := by
  rw [equal_scores ge]
  exact R52.ThreeCover.unrestricted_iff ge

theorem Covered.mono {S : Finset Point} {δ η : ℝ} (h : Covered S δ) (le : δ≤η) : Covered S η := by
  obtain ⟨p,hp,q,hq,pq,c,cover⟩:=h
  refine ⟨p,hp,q,hq,pq,c,?_⟩
  intro x hx
  obtain ⟨i,hi⟩:=cover x hx
  exact ⟨i,hi.trans (mul_le_mul_of_nonneg_right le dist_nonneg)⟩

theorem unrestricted_iff_minimizing_sequence {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔ ∃ S : ℕ→Finset Point,
      (∀ m,(S m).card=N) ∧ Tendsto (fun m=>maxAngle (S m)) atTop (𝓝 (alpha N)) ∧
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
    have near : ∀ᶠ m in atTop,maxAngle (S m)<alpha N+δ := lim.eventually_lt tendsto_const_nhds (lt_add_of_pos_right _ dp)
    obtain ⟨m,em,ang⟩:=(small.and near).exists
    exact ⟨S m,size m,ang,(cover m).mono em.le⟩

end R53.FourCover
#print axioms R53.FourCover.full_staircase
#print axioms R53.FourCover.equal_scores
#print axioms R53.FourCover.unrestricted_iff_minimizing_sequence
