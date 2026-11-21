import NormalizedFiveGap

universe u
noncomputable section
namespace R94.Enclosed
open JSP404 Real InnerProductGeometry R55.WeightedCollision R89.Sharp

/-- A single margin applies after selecting five sites in any finite weighted
support. D may be any upper radius from the selected marked site. -/
theorem selected_scale_gap {W : ℕ} (wp : 0<W) {ρ : ℝ} (rp : 0<ρ) :
    ∃ε : ℝ,0<ε ∧ ∀{I : Type u} [Fintype I] (c : I→Point),Function.Injective c →
      ∀(w : I→ℕ),(∀i,0<w i) → ∀(e : Fin 5↪I),W≤w (e 0) →
      c (e 0)∈convexHull ℝ ((fun j=>c (e j)) '' {j | j≠0}) →
      ∀D : ℝ,0<D → (∀j,dist (c (e j)) (c (e 0))≤D) →
      (∀i j,i≠j→ρ*D≤dist (c (e i)) (c (e j))) →
      ∀θ∈attainable w c,criticalAngle W+ε≤θ := by
  obtain ⟨ε,ep,law⟩:=normalized_gap wp rp
  refine ⟨ε,ep,?_⟩
  intro I inst c ci w pos e heavy enc D dp bound sep θ hit
  let a (j : Fin 5):=c (e j)
  have ai : Function.Injective a:=ci.comp e.injective
  let L : Point→ₗ[ℝ]Point:=D⁻¹ • LinearMap.id
  let F : Point→ᵃ[ℝ]Point:=L.toAffineMap.comp (AffineEquiv.vaddConst ℝ (a 0)).symm.toAffineMap
  let b (j : Fin 5):=F (a j)
  have form (j : Fin 5): b j=D⁻¹ • (a j-a 0):=rfl
  have delta (j k : Fin 5) : b j-b k=D⁻¹ • (a j-a k):=by
    rw [form,form,←smul_sub];congr 1;abel
  have scale (j k : Fin 5) : dist (b j) (b k)=dist (a j) (a k)/D :=by
    rw [dist_eq_norm,delta,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr dp),
      ←dist_eq_norm,div_eq_inv_mul]
  have bi : Function.Injective b:=by
    intro i j eq
    apply ai
    apply dist_eq_zero.mp
    have h:=scale i j
    rw [eq,dist_self] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right dp.ne'
  have bound' (j : Fin 5) : dist (b j) 0≤1:=by
    have zero : b 0=0:=by rw [form];simp
    rw [←zero,scale,div_le_iff₀ dp,one_mul]
    exact bound j
  have sep' (i j : Fin 5) (ij : i≠j) : ρ≤dist (b i) (b j):= by
    rw [scale,le_div_iff₀ dp];exact sep i j ij
  have enc' : b 0∈convexHull ℝ (b '' {j | j≠0}) := by
    have h : F (a 0)∈F '' convexHull ℝ (a '' {j | j≠0}) :=⟨_,enc,rfl⟩
    rw [F.image_convexHull,Set.image_image] at h
    exact h
  let : Nontrivial I:=⟨e 0,e 1,e.injective.ne (by decide : (0:Fin 5)≠1)⟩
  obtain ⟨nonneg,mac,v,unit,inter,out⟩:=(R54.Profile.fixed_profile pos (fun j=>exists_ne j) ci).mp hit
  have axes : Admissible (w ∘ e) b θ := by
    refine ⟨nonneg,?_,fun j=>v (e j),fun i j=>unit _ _,fun i=>inter (e i),?_⟩
    · intro i j k ij ik jk
      change angle (b i-b j) (b k-b j)≤θ
      rw [delta,delta,angle_smul_left_of_pos _ _ (inv_pos.mpr dp),angle_smul_right_of_pos _ _ (inv_pos.mpr dp)]
      exact mac (e i) (e j) (e k) (e.injective.ne ij) (e.injective.ne ik) (e.injective.ne jk)
    · intro i j ij u r hr
      rw [delta,angle_smul_right_of_pos _ _ (inv_pos.mpr dp)]
      exact out (e i) (e j) (e.injective.ne ij) u r hr
  have fits (j : Fin 5) : marked W j≤2^(dim (w ∘ e) j) := by
    apply le_trans _ (Nat.le_pow_clog (by decide : 1<2) (w (e j)))
    by_cases zero : j=0
    · subst j;simpa [marked] using heavy
    · simpa [marked,zero] using (show 1≤w (e j) by have:=pos (e j);omega)
  exact law b bound' sep' enc' θ (transfer (marked_pos wp) fits bi axes)

/-- Relative separation measured against the diameter of the entire original
support. Arbitrary additional centers and arbitrary other weights are allowed. -/
theorem selected_diameter_gap {W : ℕ} (wp : 0<W) {ρ : ℝ} (rp : 0<ρ) :
    ∃ε : ℝ,0<ε ∧ ∀{I : Type u} [Fintype I] (c : I→Point),Function.Injective c →
      ∀(w : I→ℕ),(∀i,0<w i) → ∀(e : Fin 5↪I),W≤w (e 0) →
      c (e 0)∈convexHull ℝ ((fun j=>c (e j)) '' {j | j≠0}) →
      (∀i j,i≠j→ρ*Metric.diam (Set.range c)≤dist (c (e i)) (c (e j))) →
      ∀θ∈attainable w c,criticalAngle W+ε≤θ := by
  obtain ⟨ε,ep,law⟩:=selected_scale_gap wp rp
  refine ⟨ε,ep,?_⟩
  intro I inst c ci w pos e heavy enc sep
  have bd:= (Set.finite_range c).isBounded
  have bound (i j : I):=Metric.dist_le_diam_of_mem bd (Set.mem_range_self i) (Set.mem_range_self j)
  have dp : 0<Metric.diam (Set.range c):=(dist_pos.mpr (ci.ne (e.injective.ne
    (by decide : (0:Fin 5)≠1)))).trans_le (bound (e 0) (e 1))
  exact law c ci w pos e heavy enc _ dp (fun j=>bound (e j) (e 0)) sep

/-- The optimal attainable angle itself has the same uniform lower bound.
Three prescribed witnesses of enclosure suffice; the fifth selected center
need only satisfy the separation inequality. -/
theorem surrounded_minimum_gap {W : ℕ} (wp : 0<W) {ρ : ℝ} (rp : 0<ρ) :
    ∃ε : ℝ,0<ε ∧ ∀{I : Type u} [Fintype I] (c : I→Point),Function.Injective c →
      ∀(w : I→ℕ),(∀i,0<w i) → ∀(e : Fin 5↪I),W≤w (e 0) →
      ∀(h : Fin 3↪Fin 5),(∀k,h k≠0) →
      c (e 0)∈convexHull ℝ (Set.range (fun k=>c (e (h k)))) →
      (∀i j,i≠j→ρ*Metric.diam (Set.range c)≤dist (c (e i)) (c (e j))) →
      criticalAngle W+ε≤R54.Profile.minimum w c := by
  obtain ⟨ε,ep,law⟩:=selected_diameter_gap.{u} wp rp
  refine ⟨ε,ep,?_⟩
  intro I inst c ci w pos e heavy h off inside sep
  let : Nontrivial I:=⟨e 0,e 1,e.injective.ne (by decide : (0:Fin 5)≠1)⟩
  apply law c ci w pos e heavy _ sep _ (R54.Profile.fixed_minimum pos (fun j=>exists_ne j) ci).1.1
  apply convexHull_mono _ inside
  rintro _ ⟨k,rfl⟩
  exact ⟨h k,off k,rfl⟩

end R94.Enclosed
#print axioms R94.Enclosed.selected_scale_gap
#print axioms R94.Enclosed.selected_diameter_gap
#print axioms R94.Enclosed.surrounded_minimum_gap
