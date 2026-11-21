import ProfileSamples
noncomputable section
namespace R54.Profile
open JSP404 R56.Decorated Real Filter Topology InnerProductGeometry

/-- A simultaneous compactness lemma for all the axes at every center. Limits of two
axes in one fiber keep their signed separation, including at equality. -/
theorem axes_closed {I : Type*} [Fintype I] {d : I→ℕ} {c : I→Point}
    (ci : Function.Injective c) {θ : ℝ} {b : ℕ→I→Point} {h : ℕ→ℝ}
    (bc : ∀ i,Tendsto (fun n=>b n i) atTop (𝓝 (c i))) (hc : Tendsto h atTop (𝓝 θ))
    (A : ∀ n,Axes (b n) d (h n)) (unit : ∀ n i j,‖(A n).v i j‖=1) :
    ∃ V : Axes c d θ,∀ i j,‖V.v i j‖=1 := by
  classical
  let K:= (i : I) × Fin (d i)
  let U (n : ℕ) (x : K) := (A n).v x.1 x.2
  let C : Set (K→Point) := Set.univ.pi (fun _=>Metric.sphere (0:Point) 1)
  have compact : IsCompact C := isCompact_univ_pi (fun _=>isCompact_sphere (0:Point) 1)
  have inside (n : ℕ) : U n∈C := by
    intro x _
    simpa [Metric.mem_sphere,U] using unit n x.1 x.2
  obtain ⟨v,vin,φ,mono,lim⟩:=compact.tendsto_subseq inside
  have norm (x : K) : ‖v x‖=1 := by
    have p:=vin x (Set.mem_univ x)
    simpa [Metric.mem_sphere] using p
  have nz (x : K) : v x≠0 := by intro eq;simpa [eq] using norm x
  have conv (x : K) : Tendsto (fun n=>U (φ n) x) atTop (𝓝 (v x)) :=
    (tendsto_pi_nhds.mp lim) x
  have sneq (s : ℝ) (hs : s= -1 ∨ s=1) : s≠0 := by rcases hs with rfl|rfl <;> norm_num
  have int (i : I) (x y : Fin (d i)) (ne : x≠y) (r s : ℝ) (hr : r= -1 ∨ r=1) (hs : s= -1 ∨ s=1) :
      angle (r • v ⟨i,x⟩) (s • v ⟨i,y⟩)≤θ := by
    have pu := angle_lim (smul_ne_zero (sneq r hr) (nz ⟨i,x⟩)) (smul_ne_zero (sneq s hs) (nz ⟨i,y⟩))
      (tendsto_const_nhds.smul (conv ⟨i,x⟩)) (tendsto_const_nhds.smul (conv ⟨i,y⟩))
    exact le_of_tendsto_of_tendsto' pu (hc.comp mono.tendsto_atTop)
      (fun n=>(A (φ n)).internal i x y ne r s hr hs)
  have out (i j : I) (ne : i≠j) (x : Fin (d i)) (s : ℝ) (hs : s= -1 ∨ s=1) :
      angle (s • v ⟨i,x⟩) (c j-c i)≤θ := by
    have pu := angle_lim (smul_ne_zero (sneq s hs) (nz ⟨i,x⟩)) (sub_ne_zero.mpr (ci.ne ne.symm))
      (tendsto_const_nhds.smul (conv ⟨i,x⟩)) (((bc j).comp mono.tendsto_atTop).sub ((bc i).comp mono.tendsto_atTop))
    exact le_of_tendsto_of_tendsto' pu (hc.comp mono.tendsto_atTop)
      (fun n=>(A (φ n)).outside i j ne x s hs)
  exact ⟨⟨fun i j=>v ⟨i,j⟩,fun i j=>nz ⟨i,j⟩,int,out⟩,fun i j=>norm ⟨i,j⟩⟩

end R54.Profile
#print axioms R54.Profile.axes_closed
