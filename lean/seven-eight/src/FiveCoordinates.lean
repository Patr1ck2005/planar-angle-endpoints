import GapFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
noncomputable section
namespace R64.Five
open JSP404 Real R54.GapTest InnerProductGeometry

def X : Fin 5→ℚ := ![-101/100,-99/100,0,99/100,101/100]
def Y : Fin 5→ℚ := ![17/1600,-17/1600,5/8,-17/1600,17/1600]
def slope (i j : Fin 5) := (Y j-Y i)/(X j-X i)
def seq : Fin 5→Fin 4→Fin 5 :=
  ![![1,3,4,2], ![0,3,4,2], ![3,4,0,1], ![2,0,1,4], ![2,0,1,3]]
def low (i : Fin 5) := slope i (seq i 0)
def high (i : Fin 5) := slope i (seq i 3)
abbrev opposed (i j k : Fin 5) := (j < i ∧ i < k) ∨ (k < i ∧ i < j)

set_option maxRecDepth 9000
set_option maxHeartbeats 650000

theorem x_order : StrictMono X := by
  have c : ∀i j : Fin 5,i < j → X i < X j := by decide +kernel
  exact fun _ _ h=>c _ _ h

theorem seq_ne : ∀i k,seq i k≠i := by decide +kernel
theorem seq_cover : ∀i j,i≠j → ∃k,seq i k=j := by decide +kernel
theorem seq_mono : ∀i (j k : Fin 4), j≤k → slope i (seq i j)≤slope i (seq i k) := by decide +kernel
theorem extremes : ∀i,-(17/16:ℚ)≤low i ∧ low i≤0 ∧ 0≤high i ∧ high i≤17/16 ∧
    17/16≤high i-low i ∧ high i-low i≤7/4 := by decide +kernel
theorem slope_bound : ∀i j, i≠j → low i≤slope i j ∧ slope i j≤high i := by decide +kernel
theorem opposite_slopes : ∀i j k,opposed i j k →
    (slope i j≤0 ∧ 0≤slope i k ∧ 17/16≤slope i k-slope i j) ∨
    (slope i k≤0 ∧ 0≤slope i j ∧ 17/16≤slope i j-slope i k) := by decide +kernel

def point (l : ℝ) (i : Fin 5) : Point := !₂[(X i:ℝ),l*(Y i:ℝ)]
def heading (l : ℝ) (i j : Fin 5) := arctan (l*(slope i j:ℝ))

theorem injective (l : ℝ) : Function.Injective (point l) := by
  intro i j e
  apply x_order.injective
  have h:=congrArg (fun x : Point=>x 0) e
  change (X i:ℝ)=(X j:ℝ) at h
  exact_mod_cast h

theorem chord (l : ℝ) (i j : Fin 5) (ne : i≠j) :
    point l j-point l i=(((X j:ℝ)-(X i:ℝ))*√(1+(l*(slope i j:ℝ))^2)) • circleDirection (heading l i j) := by
  have nz : (X j:ℝ)-(X i:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast x_order.injective.ne ne.symm)
  have sn : √(1+(l*(slope i j:ℝ))^2)≠0 := ne_of_gt (by positivity)
  ext k; fin_cases k  <;> simp [point,circleDirection,heading,cos_arctan,sin_arctan]
  · field_simp
  · have h : (slope i j:ℝ)=((Y j:ℝ)-(Y i:ℝ))/((X j:ℝ)-(X i:ℝ)) := by simp [slope]
    field_simp [sn]
    rw [h];field_simp

theorem forward {i j : Fin 5} (lt : i < j) (l : ℝ) :
    ∃r : ℝ,0 < r ∧ point l j-point l i=r • circleDirection (heading l i j) := by
  have dx : (X i:ℝ) < (X j:ℝ) := by exact_mod_cast x_order lt
  let z:=√(1+(l*(slope i j:ℝ))^2)
  have zp : 0 < z := Real.sqrt_pos.mpr (by positivity)
  exact ⟨_,mul_pos (sub_pos.mpr dx) zp,chord l i j lt.ne⟩

theorem backward {i j : Fin 5} (lt : j < i) (l : ℝ) :
    ∃r : ℝ,0 < r ∧ point l j-point l i= -(r • circleDirection (heading l i j)) := by
  have dx : (X j:ℝ) < (X i:ℝ) := by exact_mod_cast x_order lt
  let s:=√(1+(l*(slope i j:ℝ))^2)
  have sp : 0 < s := Real.sqrt_pos.mpr (by positivity)
  refine ⟨_,mul_pos (sub_pos.mpr dx) sp,?_⟩
  rw [chord l i j lt.ne.symm,←neg_smul]
  change (((X j:ℝ)-(X i:ℝ))*s) • _ = (-(((X i:ℝ)-(X j:ℝ))*s)) • _
  congr 1;ring

theorem bearing {i j : Fin 5} (ne : i≠j) (l : ℝ) :
    Bearing (point l j-point l i) (heading l i j) := by
  rcases lt_or_gt_of_ne ne with a|b
  · obtain ⟨r,rp,eq⟩:=forward a l
    exact ⟨r,rp,1,Or.inr rfl,by simpa using eq⟩
  · obtain ⟨r,rp,eq⟩:=backward b l
    exact ⟨r,rp,-1,Or.inl rfl,by simpa using eq⟩

#print axioms seq_mono
#print axioms opposite_slopes
#print axioms chord
end R64.Five