import WeightedLabels

noncomputable section
namespace R55.WeightedCollision
open Real Filter Topology JSP404 InnerProductGeometry

variable {I : Type*} [Fintype I]

/-- Internal and external angle tests for the axes in a single cloud. -/
def Internal {h : I→ℕ} (v : (i : I)→Fin (h i)→Point) (θ : ℝ) : Prop :=
  ∀ i p q, p≠q → ∀ r s : ℝ, (r = -1 ∨ r = 1) → (s = -1 ∨ s = 1) →
    angle (r • v i p) (s • v i q)≤θ

def External (c : I→Point) {h : I→ℕ} (v : (i : I)→Fin (h i)→Point) (θ : ℝ) : Prop :=
  ∀ i j, i≠j → ∀ (p : Fin (h i)) (r : ℝ), (r = -1 ∨ r = 1) →
    angle (r • v i p) (c j-c i)≤θ

def Macro (c : I→Point) (θ : ℝ) : Prop :=
  ∀ i j k, i≠j → i≠k → j≠k → EuclideanGeometry.angle (c i) (c j) (c k)≤θ

private theorem outer_limit {J : Type*} [Fintype J] (c x : J→Point)
    (inj : Function.Injective (fun i=>(c i,x i))) {u : ℝ}
    (bounds : ∀ a b d, a≠b → d≠b → clusterAngle c x a b d<u) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ a b d, a≠b → d≠b →
      EuclideanGeometry.angle (perturb c x s a) (perturb c x s b) (perturb c x s d)<u := by
  apply Filter.eventually_all.mpr; intro a
  apply Filter.eventually_all.mpr; intro b
  apply Filter.eventually_all.mpr; intro d
  by_cases ab : a=b
  · exact .of_forall (by simp [ab])
  by_cases db : d=b
  · exact .of_forall (by simp [db])
  exact ((tendsto_perturb_angle c x inj ab db).eventually_lt tendsto_const_nhds
    (bounds a b d ab db)).mono (fun _ h _ _ => h)

/-- Arbitrary binary capacities and separate angle and radius tolerances. -/
theorem full_words {h : I→ℕ} (c : I→Point) (hc : Function.Injective c)
    (v : (i : I)→Fin (h i)→Point) (hv : ∀ i j, v i j≠0)
    {θ ε ρ : ℝ} (hθ : 0≤θ) (he : 0<ε) (hr : 0<ρ)
    (outer : Macro c θ) (internal : Internal v θ) (cross : External c v θ) :
    ∃ F : ClusterWord h→Point, Function.Injective F ∧
      (∀ i, F ⟨i,fun _=>false⟩=c i) ∧ (∀ a, dist (F a) (c a.1)<ρ) ∧
      maxAngle (Finset.univ.image F)<θ+ε := by
  classical
  let cc (a : ClusterWord h) := c a.1
  have cent (i j k : I) (ij : i≠j) (kj : k≠j) : EuclideanGeometry.angle (c i) (c j) (c k)≤θ := by
    by_cases e : i=k
    · subst k
      change angle (c i-c j) (c i-c j)≤θ
      rwa [angle_self (sub_ne_zero.mpr (hc.ne ij))]
    · exact outer _ _ _ ij e kj.symm
  have inner := R52.SendovCloud.inner_angles c hc v hv hθ (show 0<ε/2 by positivity) cent internal cross
  obtain ⟨t,ip,angles⟩ := ((eventually_injective_center_cluster c hc v hv).and inner).exists
  let x : ClusterWord h→Point := clusterProjection v t
  have angular := outer_limit cc x ip angles
  have close : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ a, dist (perturb cc x s a) (cc a)<ρ := by
    apply Filter.eventually_all.mpr; intro a
    have continuous : Continuous (fun s : ℝ => cc a+s • x a) := by fun_prop
    have lim : Tendsto (fun s : ℝ => perturb cc x s a) (𝓝[>] 0) (𝓝 (cc a)) := by
      simpa [perturb] using (continuous.continuousAt (x:=0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
    exact (tendsto_iff_dist_tendsto_zero.mp lim).eventually_lt tendsto_const_nhds hr
  obtain ⟨s,inj,rad,ang⟩ := ((eventually_injective_perturb cc x ip).and (close.and angular)).exists
  let F := perturb cc x s
  refine ⟨F,inj,?_,rad,?_⟩
  · intro i
    simp [F,perturb,cc,x,clusterProjection,binaryProjection,realDigit]
  · have upper : maxAngle (Finset.univ.image F)≤θ+ε/2 := by
      apply maxAngle_le (by linarith)
      intro A hA B hB D hD ab ad bd
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hD
      exact (ang a b d (fun e=>ab (congrArg F e)) (fun e=>bd (congrArg F e.symm))).le
    linarith

/-- Arbitrary positive prescribed multiplicities wᵢ up to the supplied binary
capacities. The zero label of each fiber stays at the exact macroscopic center. -/
theorem exact_weights {h w : I→ℕ} (hw : ∀ i, 0<w i) (fits : ∀ i, w i≤2^(h i))
    (c : I→Point) (hc : Function.Injective c) (v : (i : I)→Fin (h i)→Point)
    (hv : ∀ i j, v i j≠0) {θ ε ρ : ℝ} (hθ : 0≤θ) (he : 0<ε) (hr : 0<ρ)
    (outer : Macro c θ) (internal : Internal v θ) (cross : External c v θ) :
    ∃ f : Label w→Point, Function.Injective f ∧ (∀ i, f (representative hw i)=c i) ∧
      (∀ a, dist (f a) (c a.1)<ρ) ∧ maxAngle (points f)<θ+ε := by
  obtain ⟨E,ei,home,fix⟩ := insert_labels w h hw fits
  obtain ⟨F,fi,rep,rad,cap⟩ := full_words c hc v hv hθ he hr outer internal cross
  let f := F ∘ E
  refine ⟨f,fi.comp ei,?_,?_,?_⟩
  · intro i; simp only [f,Function.comp_apply,fix,rep]
  · intro a; simpa only [f,Function.comp_apply,home] using rad (E a)
  · apply lt_of_le_of_lt (maxAngle_mono ?_) cap
    intro z hz
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image_of_mem F (Finset.mem_univ (E x))

/-- Threshold spectrum used by an arbitrary fixed-center collision model. -/
theorem mem_attainable {w : I→ℕ} (hw : ∀ i, 0<w i) (c : I→Point)
    (hc : Function.Injective c) (v : (i : I)→Fin (dim w i)→Point)
    (hv : ∀ i j, v i j≠0) {θ : ℝ} (hθ : 0≤θ)
    (outer : Macro c θ) (internal : Internal v θ) (cross : External c v θ) :
    θ∈attainable w c := by
  intro ε he
  obtain ⟨f,inj,_,rad,cap⟩ := exact_weights hw (fun i=>Nat.le_pow_clog (by decide : 1<2) (w i))
    c hc v hv hθ he he outer internal cross
  exact ⟨f,inj,rad,cap⟩

#print axioms full_words
#print axioms exact_weights
#print axioms mem_attainable
end R55.WeightedCollision
