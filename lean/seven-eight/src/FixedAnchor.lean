import TwoAnchorCount

namespace TwoAnchorCount
open Real TwoAnchorGeometry
open InnerProductGeometry

/-- The normalized second anchor. The first is the origin. -/
noncomputable def base : Plane := !₂[1,0]

private theorem plane_ext {p q : Plane} (h₀ : p 0=q 0) (h₁ : p 1=q 1) : p=q := by
  ext i
  exact Fin.cases h₀ (fun j => Fin.cases h₁ (fun k => Fin.elim0 k) j) i

private theorem base_ray : base = ray 0 := by
  apply plane_ext
  · change 1 = cos 0
    simp
  · change 0 = sin 0
    simp

private theorem neg_base_ray : -base = ray π := by
  apply plane_ext
  · change -(1:ℝ) = cos π
    simp
  · change -(0:ℝ) = sin π
    simp

/-- Positive-x polar decomposition with the actual arctangent bearing. -/
private theorem right_polar (x y : ℝ) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ x = r*cos (arctan (y/x)) ∧ y = r*sin (arctan (y/x)) := by
  let a := arctan (y/x)
  have hc : 0 < cos a := cos_arctan_pos _
  have ht : sin a / cos a = y/x := by rw [← tan_eq_sin_div_cos]; exact tan_arctan _
  refine ⟨x/cos a,div_pos hx hc,?_,?_⟩
  · field_simp
    rfl
  · have he := (div_eq_div_iff hc.ne' hx.ne').mp ht
    field_simp
    linarith

/-- Every nonzero upward or horizontal chord has an actual polar
decomposition in [0,π], including both horizontal orientations. -/
private theorem upper_polar {x y : ℝ} (hy : 0 ≤ y) (hn : x ≠ 0 ∨ y ≠ 0) :
    ∃ u r : ℝ, (0 ≤ u ∧ u ≤ π) ∧ 0 < r ∧ x=r*cos u ∧ y=r*sin u := by
  rcases eq_or_lt_of_le hy with h | h
  · subst y
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exact ⟨π,-x,⟨pi_pos.le,le_rfl⟩,by linarith,by simp,by simp⟩
    · simp [hx] at hn
    · exact ⟨0,x,⟨le_rfl,pi_pos.le⟩,hx,by simp,by simp⟩
  · obtain ⟨r,hr,hey,hex⟩ := right_polar y x h
    refine ⟨π/2 - arctan (x/y),r,⟨by linarith [arctan_lt_pi_div_two (x/y)],
      by linarith [neg_pi_div_two_lt_arctan (x/y)]⟩,hr,?_,?_⟩
    · simpa only [cos_pi_div_two_sub] using hex
    · simpa only [sin_pi_div_two_sub] using hey

theorem polar_chord {p q : Plane} (hpq : p ≠ q) (hy : p 1 ≤ q 1) :
    ∃ u r : ℝ, (0 ≤ u ∧ u ≤ π) ∧ 0 < r ∧ q-p = r • ray u := by
  have hn : q 0-p 0 ≠ 0 ∨ q 1-p 1 ≠ 0 := by
    by_contra! hh
    exact hpq (plane_ext (by linarith [hh.1]) (by linarith [hh.2]))
  obtain ⟨u,r,hu,hr,h₀,h₁⟩ := upper_polar (sub_nonneg.mpr hy) hn
  exact ⟨u,r,hu,hr,plane_ext h₀ h₁⟩

/-- The two anchor inclinations and the positive factors of the actual
position vectors in the unit strip. -/
private theorem anchor_polar (p : Plane) (hx : 0<p 0 ∧ p 0<1) :
    ∃ r s : ℝ, 0<r ∧ 0<s ∧
      p = r • ray (arctan (p 1/p 0)) ∧
      p-base = s • ray (π-arctan (p 1/(1-p 0))) := by
  obtain ⟨r,hr,hx₁,hy₁⟩ := right_polar (p 0) (p 1) hx.1
  obtain ⟨s,hs,hx₂,hy₂⟩ := right_polar (1-p 0) (p 1) (by linarith [hx.2])
  refine ⟨r,s,hr,hs,plane_ext hx₁ hy₁,plane_ext ?_ ?_⟩
  · change p 0-1=s*cos (π-arctan _)
    rw [cos_pi_sub]
    linarith
  · change p 1-0=s*sin (π-arctan _)
    simpa using hy₂

/-- Legality for all pairwise-distinct triples of the actual point set. -/
def Legal (S : Set Plane) (lam : ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r →
    angle (p-q) (r-q) ≤ π-lam

/-- Ordinary count for two fixed anchors in a normalized upper-half-plane
chart. Only Cartesian point data and ordinary Euclidean angle conditions
are inputs. The order, chord factors, minimum and short covering interval
are all consequences. The total size including the anchors is at most
2 + 2^(floor(π/λ)-2). -/
theorem fixed_anchor_count {I : Type*} [Fintype I]
    (P : I → Plane) (hinj : Function.Injective P) {lam : ℝ}
    (hl : 0<lam) (hlπ : lam ≤ π) (hn : 2 ≤ ⌊π/lam⌋₊)
    (hx : ∀ i, 0<P i 0 ∧ P i 0<1) (hy : ∀ i, 0<P i 1)
    (narrowA : ∀ i, angle base (P i) < lam)
    (narrowB : ∀ i, angle (-base) (P i-base) < lam)
    (legal : Legal (({0,base} : Set Plane) ∪ Set.range P) lam) :
    Fintype.card I ≤ 2^(⌊π/lam⌋₊-2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr inhabited =>
    let a i := arctan (P i 1 / P i 0)
    let b i := arctan (P i 1 / (1-P i 0))
    have ar (i : I) : 0 < a i ∧ a i < π/2 :=
      ⟨arctan_pos.mpr (div_pos (hy i) (hx i).1),arctan_lt_pi_div_two _⟩
    have br (i : I) : 0 < b i ∧ b i < π/2 :=
      ⟨arctan_pos.mpr (div_pos (hy i) (by linarith [(hx i).2])),arctan_lt_pi_div_two _⟩
    choose ra rb hra hrb hpa hpb using fun i => anchor_polar (P i) (hx i)
    have poleA (i : I) : P i ≠ 0 := by
      intro h
      have z := congrArg (fun q : Plane => q 0) h
      change P i 0=0 at z
      linarith [(hx i).1]
    have poleB (i : I) : P i ≠ base := by
      intro h
      have z := congrArg (fun q : Plane => q 0) h
      change P i 0=1 at z
      linarith [(hx i).2]
    have poles : (0:Plane) ≠ base := by
      intro h
      have z := congrArg (fun q : Plane => q 0) h
      change (0:ℝ)=1 at z
      linarith
    let S := ({0,base} : Set Plane) ∪ Set.range P
    have h0 : (0:Plane) ∈ S := Or.inl (by simp)
    have h1 : base ∈ S := Or.inl (by simp)
    have hm (i : I) : P i ∈ S := Or.inr ⟨i,rfl⟩
    have hupA (i : I) : 0≤a i ∧ a i≤π := ⟨(ar i).1.le,by linarith [(ar i).2,pi_pos]⟩
    have hupB (i : I) : 0≤π-b i ∧ π-b i≤π := ⟨by linarith [(br i).2,pi_pos],by linarith [(br i).1]⟩
    have ha (i : I) : 0<a i ∧ a i<lam := by
      have h := narrowA i
      rw [base_ray,hpa i,angle_smul_right_of_pos _ _ (hra i),
        angle_rays ⟨le_rfl,pi_pos.le⟩ (hupA i),zero_sub,abs_neg,abs_of_nonneg (hupA i).1] at h
      exact ⟨(ar i).1,h⟩
    have hb (i : I) : 0<b i ∧ b i<lam := by
      have h := narrowB i
      rw [neg_base_ray,hpb i,angle_smul_right_of_pos _ _ (hrb i),
        angle_rays ⟨pi_pos.le,le_rfl⟩ (hupB i)] at h
      have eq : π-(π-b i)=b i := by ring
      rw [eq,abs_of_pos (br i).1] at h
      exact ⟨(br i).1,h⟩
    have negA (i : I) : 0-P i = -(ra i • ray (a i)) := by rw [←hpa i,zero_sub]
    have negB (i : I) : base-P i = -(rb i • ray (π-b i)) := by rw [←hpb i]; abel
    have sumAB (i : I) : lam ≤ a i + b i := by
      have h := legal 0 h0 (P i) (hm i) base h1 (poleA i).symm (poleB i) poles
      rw [negA i,negB i,angle_neg_neg,angle_smul_left_of_pos _ _ (hra i),
        angle_smul_right_of_pos _ _ (hrb i),angle_rays (hupA i) (hupB i),
        abs_of_nonpos (by linarith [(ar i).2,(br i).2])] at h
      linarith
    let R (i j : I) := i ≠ j ∧ P i 1 ≤ P j 1
    have existsEdge (i j : I) : ∃ u r : ℝ, R i j →
        (0 ≤ u ∧ u ≤ π) ∧ 0<r ∧ P j-P i=r • ray u := by
      by_cases h : R i j
      · obtain ⟨u,r,hs⟩ := polar_chord (hinj.ne h.1) h.2
        exact ⟨u,r,fun _ => hs⟩
      · exact ⟨0,0,fun z => (h z).elim⟩
    choose u r edge using existsEdge
    have laws (i j : I) (h : R i j) :
        angle (ray (u i j)) (-(ray (a i))) ≤ π-lam ∧
        angle (ray (u i j)) (-(ray (π-b i))) ≤ π-lam := by
      have hA := legal (P j) (hm j) (P i) (hm i) 0 h0 (hinj.ne h.1.symm) (poleA i) (poleA j)
      have hB := legal (P j) (hm j) (P i) (hm i) base h1 (hinj.ne h.1.symm) (poleB i) (poleB j)
      rw [(edge i j h).2.2,negA i,angle_smul_left_of_pos _ _ (edge i j h).2.1,
        angle_neg_right,angle_smul_right_of_pos _ _ (hra i)] at hA
      rw [(edge i j h).2.2,negB i,angle_smul_left_of_pos _ _ (edge i j h).2.1,
        angle_neg_right,angle_smul_right_of_pos _ _ (hrb i)] at hB
      simpa only [angle_neg_right] using And.intro hA hB
    have interval (i j : I) (h : R i j) := upward_chord_interval (ha i) (hb i) hlπ
      (edge i j h).1 (laws i j h).1 (laws i j h).2
    have inc (i j : I) (h : R i j) : a i<a j ∧ b i<b j := by
      have had := hpa i
      have hbd := hpb i
      have hz := (edge i j h).2.2
      have xa := congrArg (fun q : Plane => q 0) had
      have ya := congrArg (fun q : Plane => q 1) had
      have xb := congrArg (fun q : Plane => q 0) hbd
      have yb := congrArg (fun q : Plane => q 1) hbd
      change P i 0-1=rb i*cos (π-b i) at xb
      change P i 1-0=rb i*sin (π-b i) at yb
      rw [cos_pi_sub] at xb
      rw [sub_zero,sin_pi_sub] at yb
      exact anchor_inclinations_increase (hx i) (hx j) ⟨hra i,hrb i,(edge i j h).2.1⟩
        ⟨xa,ya⟩ ⟨by linarith,yb⟩
        ⟨congrArg (fun q : Plane => q 0) hz,congrArg (fun q : Plane => q 1) hz⟩
        (ha i) (hb i) hlπ (edge i j h).1 (laws i j h).1 (laws i j h).2
    obtain ⟨z,_,hz⟩ := Finset.exists_min_image Finset.univ (fun i => P i 1) Finset.univ_nonempty
    have mins (i : I) : a z ≤ a i ∧ b z ≤ b i := by
      by_cases he : z=i
      · simp [he]
      · have hi := inc z i ⟨he,hz i (Finset.mem_univ _)⟩
        exact ⟨hi.1.le,hi.2.le⟩
    refine interval_count P R u (L:=lam+a z) (H:=π-lam-b z) hl ?_ ?_ ?_ ?_ ?_ ?_
    · intro i j h
      rcases le_total (P i 1) (P j 1) with h' | h'
      · exact Or.inl ⟨h,h'⟩
      · exact Or.inr ⟨h.symm,h'⟩
    · rw [Nat.cast_sub hn,Nat.cast_ofNat]
      have hpi := (div_lt_iff₀ hl).mp (Nat.lt_floor_add_one (π/lam))
      nlinarith [sumAB z]
    · intro i j h
      exact ⟨by linarith [(interval i j h).1,(mins i).1],
        by linarith [(interval i j h).2,(mins i).2]⟩
    · exact fun i j h => (edge i j h).1
    · exact fun i j h => ⟨r i j,(edge i j h).2⟩
    · intro i j k h₁ h₂
      have hik : i ≠ k := by
        intro e
        subst k
        exact (inc i j h₁).1.asymm (inc j i h₂).1
      exact legal (P i) (hm i) (P j) (hm j) (P k) (hm k) (hinj.ne h₁.1) (hinj.ne h₂.1) (hinj.ne hik)

#print axioms fixed_anchor_count
end TwoAnchorCount
