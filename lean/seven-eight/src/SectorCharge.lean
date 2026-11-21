import CriticalEndpointProfile

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention InnerProductGeometry

def sector {m : ℕ} (c : Fin m→Point) (θ : ℝ) (j : Fin m) (z : Point) : Finset (Fin m) := by
  classical
  exact univ.filter fun i=>i≠j ∧ (θ<angle z (c i-c j) ∨ θ<angle (-z) (c i-c j))

/-- A single angular sector pays at least the surplus plus the old row's entire
capacity whenever its central trial direction fits beside a saturated actual axis kit.
The sector uses true outgoing chords and both signs of that trial direction. -/
theorem sector_charge {m B v : ℕ} (three : 3≤m) {c : Fin m→Point} (ci : Function.Injective c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) {p : Fin m→ℕ} (R : ∀i,Row (p i))
    (front : Represents R c) (back : Witnessed R c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) (j : Fin m) (old : Fin (score R j (π-θ))→Point)
    (safe : InternalTrial old θ) (clear : ∀i,j≠i → Compatible old θ (c i-c j))
    (z : Point) (nz : z≠0) (fits : ∀q,∀s : ℝ,s= -1 ∨ s=1 → angle (s • z) (old q)≤θ) :
    v+mass R θ j≤∑i∈sector c θ j z,mass R θ i := by
  classical
  let V : Fin (score R j (π-θ)+1)→Point := Fin.cons z old
  have kit : InternalTrial V θ := by
    refine ⟨Fin.cases nz safe.1,?_⟩
    intro a b neq s sign
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact False.elim (neq rfl)
      | succ b => exact fits b s sign
    | succ a =>
      cases b using Fin.cases with
      | zero =>
        change angle (s • old a) z≤θ
        rcases sign with rfl|rfl
        · simpa only [neg_one_smul,angle_neg_left,angle_comm (old a) z] using fits a (-1) (Or.inl rfl)
        · simpa only [one_smul,angle_comm (old a) z] using fits a 1 (Or.inr rfl)
      | succ b => exact safe.2 a b (fun eq=>neq (congrArg Fin.succ eq)) s sign
  have sub : blockers c θ j V⊆sector c θ j z := by
    intro i mem
    obtain ⟨ij,no⟩:=(mem_filter.mp mem).2
    apply mem_filter.mpr;refine ⟨mem_univ _,ij,?_⟩
    by_contra! nothit
    apply no
    intro a s sign
    cases a using Fin.cases with
    | zero =>
      rcases sign with rfl|rfl
      · simpa only [V,Fin.cons_zero,neg_one_smul] using nothit.2
      · simpa only [V,Fin.cons_zero,one_smul] using nothit.1
    | succ a => exact clear i ij.symm a s sign
  have ch:=all_blockers three ci pos below R front back full crit j (r:=1) (by decide) V kit
  have le:=sum_le_sum_of_subset_of_nonneg (f:=mass R θ) sub (fun _ _ _=>Nat.zero_le _)
  simpa using ch.trans le

/-- The saturated old kit needed in the single-sector statement always exists for
the original complete row at the actual apex. -/
theorem physical_sectors {m B v : ℕ} (three : 3≤m) {c : Fin m→Point} (ci : Function.Injective c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) {p : Fin m→ℕ} (R : ∀i,Row (p i))
    (front : Represents R c) (back : Witnessed R c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) (j : Fin m) :
    ∃old : Fin (score R j (π-θ))→Point, InternalTrial old θ ∧
      (∀i,j≠i → Compatible old θ (c i-c j)) ∧
      ∀z : Point,z≠0 → (∀q,∀s : ℝ,s= -1 ∨ s=1 → angle (s • z) (old q)≤θ) →
        v+mass R θ j≤∑i∈sector c θ j z,mass R θ i := by
  let A:=full_axes R (sub_pos.mpr below) front
  have safe : InternalTrial (A.v j) θ := by
    refine ⟨A.nonzero j,fun k l ne s sg=>?_⟩
    simpa only [one_smul,sub_sub_cancel] using A.internal j k l ne s 1 sg (Or.inr rfl)
  have clear (i : Fin m) (ji : j≠i) : Compatible (A.v j) θ (c i-c j) := by
    intro k s sg;simpa only [sub_sub_cancel] using A.outside j i ji k s sg
  exact ⟨A.v j,safe,clear,sector_charge three ci pos below R front back full crit j (A.v j) safe clear⟩

end R85.CriticalMass
#print axioms R85.CriticalMass.sector_charge
#print axioms R85.CriticalMass.physical_sectors
