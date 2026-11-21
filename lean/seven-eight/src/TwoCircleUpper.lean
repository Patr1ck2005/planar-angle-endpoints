import CircleUpper

noncomputable section
namespace R59.Concyclic
open R58.CircleModel Real JSP404 R55.WeightedCollision Filter Topology

private def weights (r s : ℕ) (i : Fin 2) := if i=0 then r else s
private def split {r s : ℕ} (u : Label (weights r s)) : R51.TwoCenters.Labels r s :=
  if e : u.1=0 then Sum.inl ⟨u.2.val,by simpa [weights,e] using u.2.isLt⟩
  else Sum.inr ⟨u.2.val,by simpa [weights,e] using u.2.isLt⟩

private theorem split_inj {r s : ℕ} : Function.Injective (@split r s) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ eq
  fin_cases i <;> fin_cases j <;> simp [split] at eq
  all_goals exact congrArg (Sigma.mk _) (Fin.ext eq)

/-- The two distinct macroscopic limits in the R51 dyadic construction lie on
a common circle centered at their midpoint. This transfers the original limits
to the fixed, finite-weight spectrum, at the very same threshold. -/
theorem of_two {N : ℕ} {θ : ℝ} (h : θ∈R51.TwoCenters.byCard N) : θ∈scores N := by
  classical
  obtain ⟨r,s,size,two,sp,_,f,a,b,ab,left,right,inj,cap⟩:=h
  let c : Fin 2→Point:=![a,b]
  have ci : Function.Injective c := by
    intro i j e;fin_cases i <;> fin_cases j <;> simp_all [c]
  have round : OnCircle c := by
    refine ⟨midpoint ℝ a b,‖(2:ℝ)‖⁻¹*dist a b,?_⟩
    intro i;fin_cases i <;> simp [c,dist_left_midpoint,dist_right_midpoint]
  have wp (i) : 0<weights r s i := by unfold weights;split_ifs <;> omega
  refine ⟨2,by decide,c,ci,round,weights r s,wp,?_,?_⟩
  · simpa [Fin.sum_univ_two,weights] using size.symm
  · intro e ep
    have lim (x : Label (weights r s)) :
        Tendsto (fun t=>f t (split x)) (𝓝[>] (0:ℝ)) (𝓝 (c x.1)) := by
      rcases x with ⟨i,x⟩
      fin_cases i
      · simpa [split,c] using left ⟨x.val,x.isLt⟩
      · simpa [split,c] using right ⟨x.val,x.isLt⟩
    have near (x : Label (weights r s)) :
        ∀ᶠ t in 𝓝[>] (0:ℝ),dist (f t (split x)) (c x.1)<e := by
      have l:=(lim x).dist (tendsto_const_nhds (x:=c x.1))
      rw [dist_self] at l
      exact l.eventually_lt tendsto_const_nhds ep
    obtain ⟨t,one,ang,close⟩:=(inj.and ((cap e ep).and (Filter.eventually_all.mpr near))).exists
    refine ⟨f t ∘ split,one.comp split_inj,close,lt_of_le_of_lt (maxAngle_mono ?_) ang⟩
    intro z hz
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (split x))

theorem high_upper {N k : ℕ} (sz : 3≤N) (hi : N≤8*2^k) :
    π-π/((k:ℝ)+3)∈scores N := by
  have two:=of_two (R51.TwoCenters.sharp_by_card sz).1
  have count : Nat.clog 2 N≤k+3 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add];norm_num;omega
  have real : (Nat.clog 2 N:ℝ)≤(k:ℝ)+3 := by exact_mod_cast count
  have pos : 0<(Nat.clog 2 N:ℝ) := by exact_mod_cast (Nat.clog_pos (by decide : 1<2) (show 1<N by omega))
  exact increasing two (by linarith [div_le_div_of_nonneg_left pi_pos.le pos real])

#print axioms of_two
#print axioms high_upper
end R59.Concyclic

