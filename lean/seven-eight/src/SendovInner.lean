import JSP404.ThreeClusterGeometry

noncomputable section
open Filter Topology
namespace R52.SendovCloud
open JSP404 Real
set_option maxHeartbeats 1200000

/-- The inner-angle estimate from JSP404.ClusterConstruction retains the perturbation parameter for the outer limit. -/
theorem inner_angles {κ : Type*} [Fintype κ]
    {dims : κ → ℕ} (c : κ → Point) (hc : Function.Injective c)
    (v : (i : κ) → Fin (dims i) → Point) (hv : ∀ i j, v i j ≠ 0)
    {θ : ℝ} (hθ : 0 ≤ θ) {ε : ℝ} (hε : 0<ε)
    (hcenters : ∀ i j k, i ≠ j → k ≠ j → EuclideanGeometry.angle (c i) (c j) (c k) ≤ θ)
    (hinternal : ∀ i p q, p ≠ q → ∀ r s : ℝ,
      (r = -1 ∨ r = 1) → (s = -1 ∨ s = 1) →
      InnerProductGeometry.angle (r • v i p) (s • v i q) ≤ θ)
    (hcross : ∀ i j, i ≠ j → ∀ (p : Fin (dims i)) (r : ℝ), (r = -1 ∨ r = 1) →
      InnerProductGeometry.angle (r • v i p) (c j - c i) ≤ θ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a b d : ClusterWord dims, a≠b → d≠b →
      clusterAngle (fun z : ClusterWord dims => c z.1) (clusterProjection v t) a b d < θ+ε := by
  classical
  let cc : ClusterWord dims → Point := fun a => c a.1
  have htriples : ∀ a b d : ClusterWord dims, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      a ≠ b → d ≠ b → clusterAngle cc (clusterProjection v t) a b d < θ + ε := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, d⟩
    by_cases hij : i = j <;> by_cases hkj : k = j
    · subst j
      subst k
      by_cases hab : a = b
      · exact Filter.Eventually.of_forall (by simp [hab])
      by_cases hdb : d = b
      · exact Filter.Eventually.of_forall (by simp [hdb])
      have hh := eventually_binaryProjection_angle_lt (v i) (hv i) hθ hε (hinternal i) a b d hab hdb
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, EuclideanGeometry.angle,
        vsub_eq_sub] using ht
    · subst j
      by_cases hab : a = b
      · exact Filter.Eventually.of_forall (by simp [hab])
      obtain ⟨m, hm, hem⟩ := exists_first_difference hab
      have hne : c k ≠ c i := hc.ne hkj
      have hh := (tendsto_binaryProjection_direction_angle (v i) a b m hm hem (hv i m)
        (c k - c i) (sub_ne_zero.mpr hne)).eventually_lt tendsto_const_nhds
        ((hcross i k (Ne.symm hkj) m (realDigit (a m) - realDigit (b m)) (realDigit_sub_eq_sign hm)).trans_lt
          (lt_add_of_pos_right θ hε))
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, hne] using ht
    · subst k
      by_cases hdb : d = b
      · exact Filter.Eventually.of_forall (by simp [hdb])
      obtain ⟨m, hm, hem⟩ := exists_first_difference hdb
      have hne : c i ≠ c j := hc.ne hij
      have hh := (tendsto_binaryProjection_direction_angle (v j) d b m hm hem (hv j m)
        (c i - c j) (sub_ne_zero.mpr hne)).eventually_lt tendsto_const_nhds
        ((hcross j i (Ne.symm hij) m (realDigit (d m) - realDigit (b m)) (realDigit_sub_eq_sign hm)).trans_lt
          (lt_add_of_pos_right θ hε))
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, hne,
        InnerProductGeometry.angle_comm] using ht
    · have hneij : c i ≠ c j := hc.ne hij
      have hnekj : c k ≠ c j := hc.ne hkj
      apply Filter.Eventually.of_forall
      intro t _ _
      simpa [clusterAngle, clusterDirection, cc, hneij, hnekj, EuclideanGeometry.angle,
        vsub_eq_sub] using (hcenters i j k hij hkj).trans_lt (lt_add_of_pos_right θ hε)
  have hall := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr
    (fun b => Filter.eventually_all.mpr (htriples a b)))
  exact hall

end R52.SendovCloud
