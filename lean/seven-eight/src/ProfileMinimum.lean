import CollisionSpectrum
noncomputable section
namespace R54.Profile
open JSP404 R55.WeightedCollision Real InnerProductGeometry

theorem monotone {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ φ : ℝ}
    (h : θ∈attainable w c) (le : θ≤φ) : φ∈attainable w c := by
  intro e ep
  obtain ⟨f,inj,rad,cap⟩:=h e ep
  exact ⟨f,inj,rad,by linarith⟩

def minimum {I : Type*} [Fintype I] (w : I→ℕ) (c : I→Point) := sInf (attainable w c)

/-- There is a minimizing choice of directions at the exact fixed-center value,
even when no ordinary finite point set attains that angle. -/
theorem fixed_minimum {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c) :
    IsLeast (attainable w c) (minimum w c) ∧ Admissible w c (minimum w c) := by
  classical
  have unit : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : Point)‖=1 := by simp
  have piAxes : Admissible w c π := ⟨pi_pos.le,fun _ _ _ _ _ _=>EuclideanGeometry.angle_le_pi _ _ _,
    fun _ _=>EuclideanSpace.single (0 : Fin 2) (1 : ℝ),fun _ _=>unit,fun _ _ _ _ _ _ _ _=>angle_le_pi _ _,
    fun _ _ _ _ _ _=>angle_le_pi _ _⟩
  have nt : (attainable w c).Nonempty := ⟨π,admissible_mem hw ci piAxes⟩
  have below : BddBelow (attainable w c) := ⟨0,fun θ h=>((fixed_profile hw other ci).mp h).1⟩
  have member : minimum w c∈attainable w c := by
    intro e ep
    obtain ⟨t,ht,small⟩:=exists_lt_of_csInf_lt nt (show sInf (attainable w c)<minimum w c+e/2 by
      unfold minimum;linarith)
    obtain ⟨f,inj,rad,cap⟩:=ht (e/2) (by linarith)
    exact ⟨f,inj,fun x=>(rad x).trans (by linarith),by linarith⟩
  exact ⟨⟨member,fun _ h=>csInf_le below h⟩,(fixed_profile hw other ci).mp member⟩

theorem upper_ray {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c) :
    attainable w c=Set.Ici (minimum w c) := by
  ext θ
  have least:=(fixed_minimum hw other ci).1
  exact ⟨fun h=>least.2 h,fun h=>monotone least.1 h⟩

end R54.Profile
#print axioms R54.Profile.fixed_minimum
#print axioms R54.Profile.upper_ray
