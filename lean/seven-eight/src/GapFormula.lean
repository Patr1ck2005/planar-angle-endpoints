import FixedCenterGap
import GapSlots
import ProfileMinimum
noncomputable section
namespace R54.ProfileFormula
open Real JSP404 R56.Windows R56.Clearance R55.WeightedCollision R54.GapTest R54.Profile

def gaps {m : ℕ} (R : Row m) (j : Fin m) := R.w (j.val+1)-R.w j
def required {m : ℕ} (R : Row m) (d : ℕ) : ℝ := if d=0 then 0 else π-rowLimit (gaps R) d

def macroAngle {I : Type*} [Fintype I] (c : I→Point) := maxAngle (Finset.univ.image c)

def formula {I : Type*} [Fintype I] {m : I→ℕ} (R : ∀ i,Row (m i)) (c : I→Point) (w : I→ℕ) :=
  (insert (macroAngle c) (Finset.univ.image (fun i=>required (R i) (dim w i)))).max'
    ⟨_,Finset.mem_insert_self _ _⟩

theorem formula_le {I : Type*} [Fintype I] {m : I→ℕ} (R : ∀ i,Row (m i)) (c : I→Point)
    (w : I→ℕ) (θ : ℝ) : formula R c w≤θ ↔ macroAngle c≤θ ∧ ∀ i,required (R i) (dim w i)≤θ := by
  classical
  let S:=insert (macroAngle c) (Finset.univ.image (fun i=>required (R i) (dim w i)))
  have ns : S.Nonempty := ⟨_,Finset.mem_insert_self _ _⟩
  have test : formula R c w≤θ ↔ ∀ x∈S,x≤θ := Finset.max'_le_iff S ns
  rw [test]
  simp [S]

theorem macro_iff {I : Type*} [Fintype I] (c : I→Point) (ci : Function.Injective c) (θ : ℝ) :
    macroAngle c≤θ ↔ 0≤θ ∧ Macro c θ := by
  classical
  let S:=Finset.univ.image c
  have mem (i : I) : c i∈S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  constructor
  · intro h
    exact ⟨(maxAngle_nonneg _).trans h,fun i j k ij ik jk=>
      (angle_le_maxAngle (mem i) (mem j) (mem k) (ci.ne ij) (ci.ne ik) (ci.ne jk)).trans h⟩
  · rintro ⟨pos,law⟩
    apply maxAngle_le pos
    intro x hx y hy z hz xy xz yz
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hy
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hz
    exact law i j k (fun h=>xy (congrArg c h)) (fun h=>xz (congrArg c h)) (fun h=>yz (congrArg c h))

/-- The slot values are measured from the actual lifted projective gaps.
Ties and the last available slot are included. -/
theorem required_iff {I : Type*} [Fintype I] {m : I→ℕ} (R : ∀ i,Row (m i)) (i : I)
    (d : ℕ) {θ : ℝ} (pos : 0≤θ) (below : θ<π) :
    required (R i) d≤θ ↔ d≤score R i (π-θ) := by
  by_cases zero : d=0
  · simp [zero,required,pos]
  have gn (j : Fin (m i)) : 0≤gaps (R i) j := sub_nonneg.mpr ((R i).ordered (Nat.le_succ _) j.isLt)
  rw [required,if_neg zero]
  have cap:=capacity_iff (gaps (R i)) gn (Nat.pos_of_ne_zero zero) (sub_pos.mpr below)
  change d≤score R i (π-θ) ↔ π-θ≤rowLimit (gaps (R i)) d at cap
  rw [cap]
  constructor <;> intro h <;> linarith

/-- A closed formula for the full spectrum at each fixed macroscopic shape. -/
theorem spectrum {I : Type*} [Fintype I] [Nontrivial I] {m : I→ℕ}
    (R : ∀ i,Row (m i)) {c : I→Point} (ci : Function.Injective c) (front : Represents R c)
    (back : Witnessed R c) {w : I→ℕ} (hw : ∀ i,0<w i) :
    attainable w c=Set.Ici (formula R c w) := by
  ext θ
  rw [fixed_centers_iff R ci front back hw θ]
  change _ ↔ formula R c w≤θ
  rw [formula_le,macro_iff c ci]
  by_cases full : π≤θ
  · have pos : 0≤θ := pi_pos.le.trans full
    have cap : Macro c θ := fun i j k _ _ _=>(EuclideanGeometry.angle_le_pi _ _ _).trans full
    have one (i : I) : required (R i) (dim w i)≤θ := by
      unfold required
      split_ifs
      · exact pos
      · have nn : 0≤rowLimit (gaps (R i)) (dim w i) := kth_nonneg _ _
        linarith
    exact ⟨fun _=>⟨⟨pos,cap⟩,one⟩,fun _=>Or.inl full⟩
  · rw [or_iff_right full]
    constructor
    · rintro ⟨pos,law,cap⟩
      exact ⟨⟨pos,law⟩,fun i=>(required_iff R i _ pos (lt_of_not_ge full)).mpr (cap i)⟩
    · rintro ⟨⟨pos,law⟩,cap⟩
      exact ⟨pos,law,fun i=>(required_iff R i _ pos (lt_of_not_ge full)).mp (cap i)⟩

theorem minimum_eq {I : Type*} [Fintype I] [Nontrivial I] {m : I→ℕ}
    (R : ∀ i,Row (m i)) {c : I→Point} (ci : Function.Injective c) (front : Represents R c)
    (back : Witnessed R c) {w : I→ℕ} (hw : ∀ i,0<w i) : minimum w c=formula R c w := by
  have E:=(upper_ray hw (fun i=>exists_ne i) ci).symm.trans (spectrum R ci front back hw)
  exact Set.Ici_inj.mp E

end R54.ProfileFormula
#print axioms R54.ProfileFormula.spectrum
#print axioms R54.ProfileFormula.minimum_eq
