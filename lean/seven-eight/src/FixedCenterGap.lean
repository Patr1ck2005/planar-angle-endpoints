import WeightedGapTest
import CollisionSpectrum
noncomputable section
namespace R54.GapTest
open Real JSP404 InnerProductGeometry R56.Windows R55.WeightedCollision

/-- The limiting score for fixed ordinary centers and positive fiber sizes is
decided by actual macro angles and integer gap scores. This includes θ=π. -/
theorem fixed_centers_iff {I:Type*} [Fintype I] [Nontrivial I] {m:I→ℕ}
    (R:∀i,Row (m i)) {c:I→Point} (inj:Function.Injective c)
    (front:Represents R c) (back:Witnessed R c) {w:I→ℕ} (hw:∀i,0<w i) (θ:ℝ) :
    θ∈attainable w c ↔ π≤θ ∨
      (0≤θ ∧ Macro c θ ∧ ∀i,dim w i≤score R i (π-θ)) := by
  rw [R54.Profile.fixed_profile hw (fun i=>exists_ne i) inj]
  rcases le_or_gt π θ with full|below
  · simp only [full,true_or,iff_true]
    refine ⟨pi_pos.le.trans full,?_,(fun _ _=>circleDirection 0),?_,?_,?_⟩
    · intro i j k _ _ _;exact (angle_le_pi _ _).trans full
    · intro i p;exact norm_circleDirection 0
    · intro i p q _ r s _ _;exact (angle_le_pi _ _).trans full
    · intro i j _ p r _;exact (angle_le_pi _ _).trans full
  · simp only [not_le.mpr below,false_or]
    simpa only [sub_sub_cancel] using (admissible_iff (w:=w) R (sub_pos.mpr below) front back)

/-- The geometric rows are fixed before the cardinalities and threshold are
specified; both directions involve ordinary clusters at these very centers. -/
theorem actual_fixed_centers {I:Type*} [Fintype I] [Nontrivial I] (c:I→Point) (inj:Function.Injective c) :
    ∃m:I→ℕ,∃R:∀i,Row (m i),Represents R c ∧ Witnessed R c ∧
    ∀(w:I→ℕ), (∀i,0<w i) → ∀θ:ℝ,
      (θ∈attainable w c ↔ π≤θ ∨ (0≤θ ∧ Macro c θ ∧ ∀i,dim w i≤score R i (π-θ))) := by
  obtain ⟨m,R,front,back⟩:=actual_rows c inj
  exact ⟨m,R,front,back,fun _ hw θ=>fixed_centers_iff R inj front back hw θ⟩

#print axioms fixed_centers_iff
#print axioms actual_fixed_centers
end R54.GapTest
