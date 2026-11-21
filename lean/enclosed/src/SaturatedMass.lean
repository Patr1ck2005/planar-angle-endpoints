import SaturatedCone
noncomputable section
open scoped Classical
namespace R66.Five
open Real JSP404 R54.GapTest R54.Profile R55.WeightedCollision R56.Windows Finset
open InnerProductGeometry R51.Anchored R37.SignedFan R49.FactorPacking

variable {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} {w : I→ℕ} {θ : ℝ}

omit [Nontrivial I] in
theorem single_wall_budget (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    (i : I) {v : Point} (nv : v≠0) {η : ℝ} (view : ∀j,i≠j → angle v (c i-c j)≤η)
    (below : θ<π) {B : ℕ} (fit : π+2*η<((B:ℝ)+2)*(π-θ)) :
    ∑j ∈ univ.erase i,w j ≤ 2^B := by
  classical
  obtain ⟨t,b,r,rt,rp,eq⟩:=signed_polar nv
  let U:=univ.erase i
  let W (a : ℕ):=if a=0 then t else t+π
  have cone : InCone (U.image c) (c i) (oriented t b) η := by
    rintro _ x
    obtain ⟨j,h,rfl⟩:=mem_image.mp x
    have h':=view j (mem_erase.mp h).1.symm
    rwa [eq,angle_smul_left_of_pos _ _ rp] at h'
  have wall (a : ℕ) (_ : a≤1) : Wall (univ.image c) (U.image c) t (W a) η := by
    refine ⟨c i,mem_image_of_mem _ (mem_univ _),?_,t,b,rt,cone,?_⟩
    · rintro member
      obtain ⟨j,jm,co⟩:=mem_image.mp member
      exact (mem_erase.mp jm).1 (ci co)
    · by_cases z : a=0
      · exact Or.inl (by simp [lifted,W,z])
      · exact Or.inr (by simp [lifted,W,z])
  have bound:=R62.Contraction.weighted_cluster ci wp hit U (m:=1) (by decide) t rt W (fun _=>η)
    (fun _=>B) (by simp [W]) (by simp [W]) wall below (by
      intro j;fin_cases j;simp [W];linarith only [fit])
  simpa using bound

private theorem row_gap_le {m : ℕ} (R : Row m) (j : Fin m) : R.w (j.val+1)-R.w j≤π := by
  have h:=R.ordered (Nat.succ_le_of_lt j.isLt) (le_refl _)
  rw [R.period] at h
  linarith only [h,R.ordered (Nat.zero_le j.val) j.isLt.le]

theorem individual_exponent (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lp : 0<π-θ) (top : π<((k:ℝ)+3)*(π-θ)) (i : I) :
    dim w i≤k+1 := by
  obtain ⟨m,R,front,back⟩:=actual_rows c ci
  have data:=(fixed_centers_iff R ci front back wp θ).mp hit
  have bits:=(data.resolve_left (not_le.mpr (sub_pos.mp lp))).2.2 i
  by_contra! big
  have sat : k+1+1≤∑j,(R i).digits j (π-θ) := le_trans big bits
  have more : π<(((k+1:ℕ):ℝ)+3)*(π-θ) := by push_cast;nlinarith
  obtain ⟨j,hh⟩:=long_gap (R i) lp more sat
  push_cast at hh
  nlinarith only [hh,top,row_gap_le (R i) j]

theorem saturated_view (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lp : 0<π-θ) (top : π<((k:ℝ)+3)*(π-θ))
    (i : I) (sat : k+1≤dim w i) :
    ∃v : Point,v≠0 ∧ ∀j,i≠j → angle v (c i-c j)≤(π-((k:ℝ)+2)*(π-θ))/2 := by
  obtain ⟨m,R,front,back⟩:=actual_rows c ci
  have data:=(fixed_centers_iff R ci front back wp θ).mp hit
  obtain ⟨pos,law,all⟩:=data.resolve_left (not_le.mpr (sub_pos.mp lp))
  obtain ⟨z,big⟩:=long_gap (R i) lp top (sat.trans (all i))
  have cover:=complement_interval R front i z
  obtain ⟨v,nv,view⟩:=viewing_cone law pos (by nlinarith only [big,top]) i cover
  exact ⟨v,nv,fun j hj=>(view j hj).trans (by linarith only [big])⟩

/-- The saturated low-band bound in the actual weighted perturbation model,
for any number of macrocenters and arbitrary scales within the fibers. -/
theorem one_large_low_mass (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (short : θ<π-2*π/(2*(k:ℝ)+5)) (i : I) (sat : k+1≤dim w i) :
    (∑j,w j)≤4*2^k := by
  classical
  have den : 0<2*(k:ℝ)+5 := by positivity
  have lp : 0<π-θ := by linarith [div_pos (show 0<2*π by positivity) den]
  have l : 2*π<(2*(k:ℝ)+5)*(π-θ) := by
    have t:=(div_lt_iff₀ den).mp (show 2*π/(2*(k:ℝ)+5)<π-θ by linarith)
    linarith only [t]
  have top : π<((k:ℝ)+3)*(π-θ) := by nlinarith only [l,lp]
  have bound:=individual_exponent ci wp hit lp top i
  obtain ⟨v,nv,view⟩:=saturated_view ci wp hit lp top i sat
  have rest:=single_wall_budget ci wp hit i nv view (sub_pos.mp lp) (B:=k+1)
    (by push_cast;nlinarith only [l])
  have full:=sum_erase_add (s:=univ) w (mem_univ i)
  have own: w i≤2^(k+1) := (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) bound)
  rw [pow_succ] at own rest
  omega

#print axioms individual_exponent
#print axioms saturated_view
#print axioms one_large_low_mass
end R66.Five