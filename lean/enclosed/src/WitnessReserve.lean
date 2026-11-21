import MeshReserve
import AllConcyclic
noncomputable section
namespace R59.Mesh
open Real JSP404 R54.GapTest R56.Windows R55.WeightedCollision

theorem separated_budget {h : ℕ} (R : Row h) {l : ℝ} (lp : 0<l)
    (wide : ∀j : Fin h,l≤R.w (j.val+1)-R.w j) :
    (∑j : Fin h,R.digits j l)+h≤⌊π/l⌋₊ := by
  let g (j : Fin h):=R.w (j.val+1)-R.w j
  have span : (∑ j,g j)=π := by
    calc _=∑ j∈Finset.range h,(R.w (j+1)-R.w j) := Fin.sum_univ_eq_sum_range _ _
         _=R.w h-R.w 0 := Finset.sum_range_sub ..
         _=_ := by rw [R.period];ring
  have each (j : Fin h) : ((R.digits j l:ℝ)+1)*l≤g j := by
    have one : 1≤⌊g j/l⌋₊ := Nat.le_floor (by rw [Nat.cast_one,le_div_iff₀ lp,one_mul];exact wide j)
    have nn : 0≤g j := lp.le.trans (wide j)
    have f:=(le_div_iff₀ lp).mp (Nat.floor_le (div_nonneg nn lp.le))
    exact le_trans (le_of_eq (by unfold Row.digits;change (((⌊g j/l⌋₊-1:ℕ):ℝ)+1)*l=(⌊g j/l⌋₊:ℝ)*l;rw [Nat.cast_sub one];push_cast;ring)) f
  have tot:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>each j)
  simp only [←Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,span,←Nat.cast_sum] at tot
  apply Nat.le_floor
  rw [Nat.cast_add,le_div_iff₀ lp]
  exact tot

theorem dyadic_of_card {N : ℕ} {θ : ℝ} (ge : 3≤N)
    (fit : θ<π → N≤2^⌊π/(π-θ)⌋₊) : π-π/(Nat.clog 2 N:ℝ)≤θ := by
  have pos : 0<(Nat.clog 2 N:ℝ) := by exact_mod_cast Nat.clog_pos (by decide : 1<2) (show 1<N by omega)
  rcases lt_or_ge θ π with lt|big
  · have d:=Nat.clog_le_of_le_pow (fit lt)
    have c : (Nat.clog 2 N:ℝ)≤π/(π-θ) :=
      (show (Nat.clog 2 N:ℝ)≤(⌊π/(π-θ)⌋₊:ℝ) by exact_mod_cast d).trans (Nat.floor_le (by positivity))
    have t:=(le_div_iff₀ (sub_pos.mpr lt)).mp c
    have small : π-θ≤π/(Nat.clog 2 N:ℝ) := (le_div_iff₀ pos).mpr (by nlinarith only [t])
    linarith
  · linarith [div_nonneg pi_pos.le pos.le]

theorem sendov_of_dyadic {N : ℕ} (ge : 3≤N) : Jsp404.alphaN N≤π-π/(Nat.clog 2 N:ℝ) :=
  (R59.Concyclic.full_staircase ge).2 (R59.Concyclic.of_two (R51.TwoCenters.sharp_by_card ge).1)

theorem witnessed_lower {I : Type*} [Fintype I] [Nontrivial I] {h : I→ℕ} (H : ℕ)
    (R : ∀i,Row (h i)) {c : I→Point} (inj : Function.Injective c) (walls : Witnessed R c)
    (range : ∀i,h i≤H) (tax : (∑ i,2^(H-h i))≤2^H)
    (apart : ∀ l,0<l→Macro c (π-l)→∀i (j : Fin (h i)),l≤(R i).w (j.val+1)-(R i).w j)
    {w : I→ℕ} (hw : ∀i,0<w i) (ge : 3≤∑i,w i) {θ : ℝ} (hit : θ∈attainable w c) :
    π-π/(Nat.clog 2 (∑i,w i):ℝ)≤θ := by
  apply dyadic_of_card ge
  intro lt
  let l:=π-θ
  have lp : 0<l := sub_pos.mpr lt
  have A : Admissible w c (π-l) := by simpa [l] using (R54.Profile.fixed_profile hw (fun i=>exists_ne i) inj).mp hit
  apply kraft w h H _ range tax
  intro i
  exact (Nat.add_le_add_right (admissible_bound R lp walls A i) _).trans (separated_budget (R i) lp (apart l lp A.2.1 i))

#print axioms witnessed_lower
#print axioms sendov_of_dyadic
end R59.Mesh