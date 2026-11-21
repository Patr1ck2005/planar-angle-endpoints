import CyclicSpectrumBound

noncomputable section
namespace R58.CircleModel
open JSP404 Real SendovCycle InnerProductGeometry R55.WeightedCollision

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

private theorem forward_index {i j : Fin t} (ne : i≠j) :
    ∃k : ℕ, (i.val < k) ∧ (k < i.val+t) ∧ C.P k=C.centers j := by
  have n : i.val≠j.val := fun e=>ne (Fin.ext e)
  rcases lt_or_gt_of_ne n with h|h
  · exact ⟨j.val,h,by omega,rfl⟩
  · exact ⟨j.val+t,by omega,by omega,C.periodic j.val⟩

/-- On the ordinary circle, consecutive three-point inequalities characterize
all macro angles, including when one of the circular gaps exceeds a semicircle. -/
theorem macro_iff_arcs (ht : 3≤t) {lam : ℝ} (lp : 0<lam) :
    Macro C.centers (π-lam) ↔ ∀n,1≤C.arc lam n+C.arc lam (n+1) := by
  refine ⟨fun h=>C.arc_legal ht lp h,?_⟩
  intro legal a i b ai _ ib
  obtain ⟨j,jlo,jhi,ej⟩ := C.forward_index ai.symm
  obtain ⟨k,klo,khi,ek⟩ := C.forward_index ib
  obtain ⟨r,rp,h⟩ := C.chord jlo jhi
  obtain ⟨s,sp,g⟩ := C.chord klo khi
  let z:=i.val+t-1
  have ends := legal z
  unfold arc at ends
  rw [←add_div,le_div_iff₀ lp] at ends
  rw [show z+1+1=(i.val+1)+t by dsimp [z];omega,C.nextPeriod] at ends
  have width : C.u z-C.u (i.val+1)≤π-lam := by linarith
  have l₁ := C.increasing.monotone (show i.val+1≤j by omega)
  have l₂ := C.increasing.monotone (show i.val+1≤k by omega)
  have h₁ := C.increasing.monotone (show j≤z by dsimp [z];omega)
  have h₂ := C.increasing.monotone (show k≤z by dsimp [z];omega)
  have bound : |C.u j-C.u k|≤π-lam := abs_le.mpr ⟨by linarith,by linarith⟩
  change angle (C.centers a-C.P i.val) (C.centers b-C.P i.val)≤π-lam
  rw [←ej,←ek,h,g,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,angle_circleDirection]
  rw [show C.u i.val+C.u j+π/2-(C.u i.val+C.u k+π/2)=C.u j-C.u k by ring,
    ←cos_abs,arccos_cos (abs_nonneg _) (by linarith)]
  exact bound

end Lift

private theorem real_seg_period {t : ℕ} {a : ℕ→ℝ} (per : ∀k,a (k+t)=a k) (n : ℕ) :
    seg a n t=seg a 0 t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e:=seg_snoc a n t
    rw [seg,per,ih] at e
    linarith

private theorem seg_append_real (a : ℕ→ℝ) (n k l : ℕ) :
    seg a n (k+l)=seg a n k+seg a (n+k) l := by
  induction l with
  | zero => simp [seg]
  | succ l ih => rw [Nat.add_succ,seg_snoc,ih,seg_snoc,Nat.add_assoc,add_assoc]

/-- Realize any strictly positive normalized cyclic arc datum on the ordinary unit
circle, with its labeled direction rows and the exact prescribed period. -/
def ofArcs {t : ℕ} (a : ℕ→ℝ) {lam : ℝ} (lp : 0<lam) (pos : ∀k,0<a k)
    (per : ∀n,a (n+t)=a n) (total : seg a 0 t=π/lam) : Lift t where
  center := 0
  radius := 1
  pos := zero_lt_one
  u := fun n=>lam*seg a 0 n
  increasing := strictMono_nat_of_lt_succ (fun n=>by
    rw [seg_snoc,Nat.zero_add]; exact mul_lt_mul_of_pos_left (lt_add_of_pos_right _ (pos n)) lp)
  nextPeriod n := by
    rw [seg_append_real,Nat.zero_add,real_seg_period per,total,mul_add]
    field_simp

theorem ofArcs_arc {t : ℕ} (a : ℕ→ℝ) {lam : ℝ} (lp : 0<lam) (pos : ∀k,0<a k)
    (per : ∀n,a (n+t)=a n) (total : seg a 0 t=π/lam) (n : ℕ) :
    (ofArcs a lp pos per total).arc lam n=a n := by
  change (lam*seg a 0 (n+1)-lam*seg a 0 n)/lam=a n
  rw [seg_snoc,Nat.zero_add,div_eq_iff lp.ne']
  ring

/-- Every positive R35 arc witness with the legal adjacent sums yields an actual
unit-circle configuration simultaneously attaining all its row capacities. -/
theorem realize_arcs {t : ℕ} (ht : 3≤t) (a : ℕ→ℝ) {lam : ℝ} (lp : 0<lam)
    (hp : 0≤π-lam) (pos : ∀k,0<a k) (per : ∀n,a (n+t)=a n)
    (total : seg a 0 t=π/lam) (legal : ∀n,1≤a n+a (n+1)) :
    ∃C : Lift t, C.center=0 ∧ C.radius=1 ∧ C.arc lam=a ∧
      π-lam∈attainable (fun i=>2^(C.budget lam i.val)) C.centers := by
  let C:=ofArcs a lp pos per total
  have arcs : C.arc lam=a := funext (ofArcs_arc a lp pos per total)
  refine ⟨C,rfl,rfl,arcs,C.attainable_maximal ht lp ((C.macro_iff_arcs ht lp).mpr ?_) hp⟩
  rwa [arcs]

#print axioms Lift.macro_iff_arcs
#print axioms realize_arcs
end R58.CircleModel

