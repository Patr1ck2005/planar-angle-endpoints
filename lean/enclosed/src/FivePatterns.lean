import MarkedReduction
import SaturatedMass
noncomputable section
namespace R66.Five
open Real JSP404 R54.Profile R55.WeightedCollision Finset

variable {c : Fin 5→Point} {w : Fin 5→ℕ} {θ : ℝ}

theorem low_pattern (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 4*2^k<∑i,w i) (hi : (∑i,w i)≤5*2^k) (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃x : Fin 5,dim w x≤k ∧ ∀j : Fin 4,dim w (x.succAbove j)=k := by
  have small : θ<π-2*π/(2*(k:ℝ)+5) := by
    have eq:=(R52.ThreeCover.full_staircase (N:=∑i,w i) (by have:=Nat.two_pow_pos k;omega)).unique
      (R52.ThreeCover.low_band lo hi)
    rwa [eq] at bad
  have limit (i) : dim w i≤k := by
    by_contra! big
    exact lo.not_ge (one_large_low_mass ci wp hit small i big)
  obtain ⟨x,_,least⟩:=Finset.exists_min_image univ (dim w) univ_nonempty
  obtain ⟨eq,sz⟩:=low_endpoint ci wp hit lo hi bad x (fun i=>least i (mem_univ _))
  refine ⟨x,sz,fun j=>le_antisymm (limit _) (le_of_not_gt (fun fewer=>?_))⟩
  have strict:=sum_lt_sum (s:=univ) (f:=fun z : Fin 4=>2^dim w (x.succAbove z)) (g:=fun _=>2^k)
    (fun z _=>Nat.pow_le_pow_right (by decide) (limit _))
    ⟨j,mem_univ _,Nat.pow_lt_pow_right (by decide) fewer⟩
  change (∑j : Fin 4,2^dim w (x.succAbove j))=_ at eq
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,eq] at strict
  exact strict.false

theorem high_pattern (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃x : Fin 5,dim w x≤k ∧ ∃p : Fin 4,dim w (x.succAbove p)=k+1 ∧
      ∀j : Fin 4,j≠p → dim w (x.succAbove j)=k := by
  classical
  have short : θ<π-π/((k:ℝ)+3) := by
    have eq:=(R52.ThreeCover.full_staircase (N:=∑i,w i) (by have:=Nat.two_pow_pos k;omega)).unique
      (R52.ThreeCover.high_band lo hi)
    rwa [eq] at bad
  have kp : 0<(k:ℝ)+3 := by positivity
  have lp : 0<π-θ := by linarith [div_pos pi_pos kp]
  have top : π<((k:ℝ)+3)*(π-θ) := by
    have t:=(div_lt_iff₀ kp).mp (show π/((k:ℝ)+3)<π-θ by linarith)
    linarith only [t]
  have exists_heavy : ∃i,2^k<w i := by
    by_contra! small
    have all:=sum_le_sum (s:=univ) (fun i _=>small i)
    simp at all
    omega
  obtain ⟨i,big⟩:=exists_heavy
  have di : dim w i=k+1 := by
    have upper:=individual_exponent ci wp hit lp top i
    have lower : k<dim w i := (Nat.lt_clog_iff_pow_lt (by decide)).mpr big
    omega
  have other (j) (ne:j≠i) : dim w j≤k := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    by_contra! large
    exact bad.not_ge (two_large_high ci wp hit lo hi ne large big)
  obtain ⟨x,_,least⟩:=Finset.exists_min_image univ (dim w) univ_nonempty
  obtain ⟨sum,sz⟩:=high_endpoint ci wp hit lo hi bad x (fun z=>least z (mem_univ _))
  have ne : i≠x := by intro e;rw [e] at di;omega
  obtain ⟨p,peq⟩:=Fin.exists_succAbove_eq ne
  refine ⟨x,sz,p,peq ▸ di,?_⟩
  let B (j : Fin 4):=if j=p then 2^(k+1) else 2^k
  have budget : (∑j,B j)=5*2^k := by
    rw [Fin.sum_univ_succAbove B p]
    simp [B,pow_succ];omega
  have limit (j : Fin 4) : 2^(dim w (x.succAbove j))≤B j := by
    by_cases eq : j=p
    · subst j;simp [B,peq,di]
    · have q : x.succAbove j≠i := fun z=>eq (x.succAbove_right_injective (z.trans peq.symm))
      simpa [B,eq] using Nat.pow_le_pow_right (by decide : 0<2) (other _ q)
  intro j jp
  have q : x.succAbove j≠i := fun z=>jp (x.succAbove_right_injective (z.trans peq.symm))
  apply le_antisymm (other _ q) (le_of_not_gt (fun fewer=>?_))
  have strict:=sum_lt_sum (s:=univ) (fun z _=>limit z)
    ⟨j,mem_univ _,by simpa [B,jp] using Nat.pow_lt_pow_right (by decide : 1<2) fewer⟩
  change fourMass (dim w) x<(∑j,B j) at strict
  omega
#print axioms low_pattern
#print axioms high_pattern
end R66.Five