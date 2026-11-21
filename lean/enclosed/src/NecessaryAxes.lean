import ProfileApproximation
import AxisCompactness
import MacroAngles
noncomputable section
namespace R54.Profile
open Real JSP404 Filter Topology InnerProductGeometry R56.Decorated

/-- A collision profile with at least two distinct macroscopic centers always admits
the full number of binary axes assigned by the rounded multiplicities. -/
theorem necessary {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (pos : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (R : Realizable w c θ) :
    0≤θ ∧ (∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ) ∧
      (∃ A : Axes c (fun i=>Nat.clog 2 (w i)) θ,∀ i j,‖A.v i j‖=1) := by
  classical
  obtain ⟨low,centers⟩:=center_bounds pos ci R
  refine ⟨low,centers,?_⟩
  by_cases full : π≤θ
  · let u : Point := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    have norm : ‖u‖=1 := by simp [u]
    have un : u≠0 := by intro z; simpa [z] using norm
    exact ⟨⟨fun _ _=>u,fun _ _=>un,fun _ _ _ _ _ _ _ _=>(angle_le_pi _ _).trans full,
      fun _ _ _ _ _ _=>(angle_le_pi _ _).trans full⟩,fun _ _=>norm⟩
  have margin : 0<(π-θ)/4 := by linarith
  let t (n : ℕ) : ℝ := min ((π-θ)/4) (1/((n:ℝ)+1))
  have positive (n : ℕ) : 0<t n := lt_min margin (by positivity)
  have zero : Tendsto t atTop (𝓝 0) := squeeze_zero (fun n=>(positive n).le)
    (fun _=>min_le_right _ _) tendsto_one_div_add_atTop_nhds_zero_nat
  have slack (n : ℕ) : θ+2*t n<π := by
    have x : t n≤(π-θ)/4 := min_le_left _ _
    linarith
  choose b near V norm using fun n=>approximating_axes pos other ci R (positive n) (slack n)
  have bc (i : I) : Tendsto (fun n=>b n i) atTop (𝓝 (c i)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _=>dist_nonneg) (fun n=>(near n i).le) zero
  have hc : Tendsto (fun n=>θ+2*t n) atTop (𝓝 θ) := by
    simpa using (tendsto_const_nhds (x:=θ)).add ((tendsto_const_nhds (x:=(2:ℝ))).mul zero)
  exact axes_closed ci bc hc V norm

end R54.Profile
#print axioms R54.Profile.necessary
