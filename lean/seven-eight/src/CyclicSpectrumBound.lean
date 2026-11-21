import CircleRowBudget
import CircleOrdering

noncomputable section
namespace R58.CircleModel
open Real JSP404 SendovCycle R54.GapTest R55.WeightedCollision R56.Windows

/-- Keeping an injectively indexed subfamily of macrocenters preserves attainment. -/
theorem restrict_attainable {I K : Type*} [Fintype I] [Fintype K] {w : I→ℕ} {c : I→Point}
    {θ : ℝ} (hit : θ∈attainable w c) (e : K→I) (ei : Function.Injective e) :
    θ∈attainable (fun i=>w (e i)) (fun i=>c (e i)) := by
  intro ε he
  obtain ⟨f,fi,near,cap⟩ := hit ε he
  let E : Label (fun i=>w (e i))→Label w := fun p=>⟨e p.1,p.2⟩
  have inj : Function.Injective E := by
    rintro ⟨x,a⟩ ⟨y,b⟩ h
    obtain rfl : x=y := ei (congrArg Sigma.fst h)
    exact congrArg (Sigma.mk x) (Sigma.mk.inj_iff.mp h).2.eq
  refine ⟨f ∘ E,fi.comp inj,fun i=>near (E i),lt_of_le_of_lt (maxAngle_mono ?_) cap⟩
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image_of_mem f (Finset.mem_univ (E i))

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

theorem spectrum_at (ht : 3≤t) {w : Fin t→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam) :
    π-lam∈attainable w C.centers ↔
    0≤π-lam ∧ Macro C.centers (π-lam) ∧ ∀i, w i≤2^(C.budget lam i.val) := by
  have N : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [fixed_centers_iff (fun i : Fin t=>C.row ht i.val) C.centers_injective
    (C.represents ht) (C.witnessed ht) hw,or_iff_right (show ¬π≤π-lam by linarith),sub_sub_cancel]
  change (_ ∧ _ ∧ ∀i, Nat.clog 2 (w i)≤C.budget lam i.val) ↔ _
  simp_rw [Nat.clog_le_iff_le_pow (by decide : 1<2)]

theorem attainable_maximal (ht : 3≤t) {lam : ℝ} (lp : 0<lam) (leg : Macro C.centers (π-lam))
    (pos : 0≤π-lam) : π-lam∈attainable (fun i=>2^(C.budget lam i.val)) C.centers :=
  (C.spectrum_at ht (fun _=>pow_pos (by decide) _) lp).mpr ⟨pos,leg,fun _=>le_rfl⟩

theorem shifted_sum (ht : 0<t) (w : Fin t→ℕ) :
    seg (fun k=>w (index ht (k+1))) 0 t=∑i,w i := by
  let f (k : ℕ) := w (index ht k)
  have per (k : ℕ) : f (k+t)=f k := by simp [f,index,Nat.add_mod_right]
  calc seg (fun k=>w (index ht (k+1))) 0 t = seg f 1 t := by
         rw [seg_fin,seg_fin];apply Finset.sum_congr rfl;intro i _;simp [f,Nat.add_comm]
       _ = seg f 0 t := seg_rotate per 1
       _ = _ := by simp [seg_fin,f,index,Nat.mod_eq_of_lt]

theorem capacity (ht : 5≤t) {w : Fin t→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam)
    (hit : π-lam∈attainable w C.centers) (hn : 3≤⌊π/lam⌋₊) (low : Bool)
    (hlow : low=true → 2*(π/lam)<2*(⌊π/lam⌋₊:ℝ)+1) :
    ∑i,w i ≤ (if low then 6 else 7)*2^(⌊π/lam⌋₊-3) := by
  obtain ⟨_,leg,hcap⟩ := (C.spectrum_at (by omega) hw lp).mp hit
  have tp : 0<t := by omega
  let b := C.charge lam
  let B := seg b 0 t
  let H (k : ℕ) := B-b k-b (k+1)+(⌊C.arc lam k+C.arc lam (k+1)⌋₊-1)
  have each (k : ℕ) : w (index tp (k+1))≤2^(H k) := by
    have h := hcap (index tp (k+1))
    change w (index tp (k+1))≤2^(C.budget lam ((k+1)%t)) at h
    rwa [(C.budget_period lam).map_mod_nat,C.budget_formula (by omega)] at h
  have total : seg (C.arc lam) 0 t=π/lam := by
    rw [C.arc_sum,Nat.zero_add,show C.u t=C.u 0+π by simpa only [Nat.zero_add] using C.nextPeriod 0]
    ring
  have cap := sharp_real_arc_capacity (C.arc lam) t ht (C.arc_period lam)
    (C.arc_nonneg lp) (C.arc_legal (by omega) lp leg) (total ▸ hn) low (total ▸ hlow)
  rw [total] at cap
  calc ∑i,w i = seg (fun k=>w (index tp (k+1))) 0 t := (shifted_sum tp w).symm
       _ ≤ seg (fun k=>2^(H k)) 0 t := by
         rw [seg_fin,seg_fin]; exact Finset.sum_le_sum (fun i _=>each (0+i.val))
       _ ≤ _ := cap

end Lift

/-- The R35 sharp circular bound applies to the *actual* arbitrary-multiplicity
fixed-center spectrum. Only ordinary point data and concyclicity enter. -/
theorem concyclic_capacity {I : Type*} [Fintype I] (size : 5≤Fintype.card I)
    (c : I→Point) (ci : Function.Injective c) (circle : OnCircle c)
    {w : I→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam) (hit : π-lam∈attainable w c)
    (hn : 3≤⌊π/lam⌋₊) (low : Bool)
    (hlow : low=true → 2*(π/lam)<2*(⌊π/lam⌋₊:ℝ)+1) :
    ∑i,w i ≤ (if low then 6 else 7)*2^(⌊π/lam⌋₊-3) := by
  classical
  have nt : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨C,e,eq⟩ := sort_circle c ci circle
  have h := restrict_attainable hit e e.injective
  rw [←funext eq] at h
  have bound := C.capacity size (fun i=>hw (e i)) lp h hn low hlow
  exact ((Equiv.sum_comp e w).symm ▸ bound)

#print axioms Lift.spectrum_at
#print axioms Lift.attainable_maximal
#print axioms concyclic_capacity
end R58.CircleModel
