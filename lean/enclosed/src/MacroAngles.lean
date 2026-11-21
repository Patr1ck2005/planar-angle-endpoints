import ProfileSamples
noncomputable section
namespace R54.Profile
open JSP404 Real Filter Topology InnerProductGeometry

theorem center_bounds {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (pos : ∀ i,0<w i) (ci : Function.Injective c) (R : Realizable w c θ) :
    0≤θ ∧ ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ := by
  classical
  let d (m : ℕ) : ℝ := 1/((m:ℝ)+1)
  have dp (m : ℕ) : 0<d m := by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f inj near cap using fun m=>R (d m) (dp m)
  have lim (i : I) : Tendsto (fun m=>f m (rep pos i)) atTop (𝓝 (c i)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _=>dist_nonneg) (fun m=>(near m (rep pos i)).le) dz
  have sc : Tendsto (fun m=>θ+d m) atTop (𝓝 θ) := by simpa using (tendsto_const_nhds (x:=θ)).add dz
  have lower : 0≤θ := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=0)) sc
    (fun m=>(maxAngle_nonneg _).trans (cap m).le)
  refine ⟨lower,?_⟩
  intro i j k ij kj
  by_cases same : i=k
  · subst k
    change angle (c i-c j) (c i-c j)≤θ
    rw [angle_self (sub_ne_zero.mpr (ci.ne ij))];exact lower
  have ang:=angle_lim (sub_ne_zero.mpr (ci.ne ij)) (sub_ne_zero.mpr (ci.ne kj))
      ((lim i).sub (lim j)) ((lim k).sub (lim j))
  apply le_of_tendsto_of_tendsto' ang sc
  intro m
  have inS (i : I) : f m (rep pos i)∈diagram (f m) := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have ri : Function.Injective (rep pos) := fun _ _ eq=>congrArg Sigma.fst eq
  exact (angle_le_maxAngle (inS i) (inS j) (inS k) ((inj m).ne (ri.ne ij)) ((inj m).ne (ri.ne same)) ((inj m).ne (ri.ne kj.symm))).trans (cap m).le

end R54.Profile
#print axioms R54.Profile.center_bounds
