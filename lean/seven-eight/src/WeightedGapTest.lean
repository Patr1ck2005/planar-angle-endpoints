import ActualGapRows
import WeightedSpectrum
noncomputable section
namespace R54.GapTest
open Real JSP404 InnerProductGeometry R56.Windows R55.WeightedCollision

variable {I:Type*} [Fintype I] {m:I→ℕ} {c:I→Point} {w:I→ℕ} {δ:ℝ}

/-- For the necessity direction each wall needs an actual external witness;
unlisted external chords can only give additional restrictions. -/
theorem admissible_bound (R:∀i,Row (m i)) (positive:0<δ) (back:Witnessed R c)
    (h:Admissible w c (π-δ)) : ∀i,dim w i≤score R i δ := by
  obtain ⟨_,_,v,unit,internal,outside⟩:=h
  have nz (i:I) (p:Fin (dim w i)) : v i p≠0:=by
    intro eq;have z:=unit i p;rw [eq,norm_zero] at z;norm_num at z
  exact axes_bound R positive back ⟨v,nz,internal,outside⟩

/-- Exact test of the shared unit-axis model for fixed centers and arbitrary
positive defect, including equality at an integral gap endpoint. -/
theorem admissible_iff (R:∀i,Row (m i)) (positive:0<δ)
    (front:Represents R c) (back:Witnessed R c) :
    Admissible w c (π-δ) ↔ 0≤π-δ ∧ Macro c (π-δ) ∧ ∀i,dim w i≤score R i δ := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,admissible_bound R positive back h⟩
  · rintro ⟨θpos,law,fits⟩
    let A:=full_axes R positive front
    let emb (i:I) : Fin (dim w i)→Fin (score R i δ):=Fin.castLE (fits i)
    refine ⟨θpos,law,fun i p=>A.v i (emb i p),?_,?_,?_⟩
    · intro i p
      exact norm_circleDirection _
    · intro i p q ne r s hr hs
      exact A.internal i _ _ (fun e=>ne (Fin.ext (congrArg (fun k:Fin (score R i δ)=>k.val) e))) r s hr hs
    · intro i j ne p r hr
      exact A.outside i j ne _ r hr

/-- The same rows simultaneously decide every defect and every weight vector.
They are obtained solely by sorting the chords between the specified centers. -/
theorem actual_gap_test [Nontrivial I] (c:I→Point) (inj:Function.Injective c) :
    ∃m:I→ℕ,∃R:∀i,Row (m i),Represents R c ∧ Witnessed R c ∧
      ∀(w:I→ℕ) (δ:ℝ),0<δ→
        (Admissible w c (π-δ) ↔ 0≤π-δ ∧ Macro c (π-δ) ∧ ∀i,dim w i≤score R i δ) := by
  obtain ⟨m,R,front,back⟩:=actual_rows c inj
  exact ⟨m,R,front,back,fun _ _ dp=>admissible_iff R dp front back⟩

theorem gap_realization (R:∀i,Row (m i)) (positive:0<δ) (front:Represents R c)
    (back:Witnessed R c) (hw:∀i,0<w i) (inj:Function.Injective c)
    (tpos:0≤π-δ) (law:Macro c (π-δ)) (fits:∀i,dim w i≤score R i δ) :
    π-δ∈attainable w c :=
  admissible_mem hw inj ((admissible_iff R positive front back).mpr ⟨tpos,law,fits⟩)

#print axioms admissible_bound
#print axioms admissible_iff
#print axioms actual_gap_test
#print axioms gap_realization
end R54.GapTest
