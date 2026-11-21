import AnchoredCloud
noncomputable section
namespace R51.Metric
open JSP404 Real InnerProductGeometry R51.Anchored
open scoped EuclideanGeometry
private theorem sight (p q x : Point) : angle (p-q) (p-x)=EuclideanGeometry.angle q p x := by
  change _=angle (q-p) (x-p)
  rw [←neg_sub q p,←neg_sub x p,angle_neg_neg]

private theorem near_angle {p q x : Point} (pq : p≠q) (near : dist x q≤dist x p) :
    EuclideanGeometry.angle x p q≤π/2 := by
  by_contra! large
  have c : cos (EuclideanGeometry.angle x p q)<0 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (show 0≤π/2 by positivity)
      (EuclideanGeometry.angle_le_pi x p q) large
  have prod : 0≤2*dist x p*dist q p := by positivity
  have law:=EuclideanGeometry.law_cos x p q
  have side:=mul_self_le_mul_self (dist_nonneg : 0≤dist x q) near
  have base : 0<dist q p := dist_pos.mpr pq.symm
  nlinarith [mul_nonpos_of_nonneg_of_nonpos prod c.le,mul_self_pos.mpr base.ne']

private theorem cell_witness {S F : Finset Point} (sub : F⊆S) {p q : Point}
    (hp : p∈S) (pq : p≠q) (ext : p∉F) (near : ∀ x∈F, dist x q≤dist x p)
    {j : ℕ} (large : 2^j<F.card) {φ : ℝ} (ph : 0<φ)
    (budget : π+2*φ≤((j:ℝ)+2)*(π-maxAngle S)) :
    ∃ x∈S, sin φ*dist p q≤dist x p ∧ sin φ*dist p q≤dist x q := by
  have two : 2≤F.card := by have := Nat.one_le_pow j 2 (by decide);omega
  have ne := Finset.card_pos.mp (show 0<F.card by omega)
  obtain ⟨x,hx,largest⟩ := F.exists_max_image (fun a=>angle (p-q) (p-a)) ne
  let θ:=angle (p-q) (p-x)
  have cone : InCone F p (p-q) θ := largest
  have bound:=anchored_budget sub two hp ext (sub_ne_zero.mpr pq) (angle_nonneg _ _) cone
  have clog : j<Nat.clog 2 F.card := by
    by_contra! h
    exact (not_le_of_gt large) ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mp h)
  have rj : (j:ℝ)+1≤Nat.clog 2 F.card := by exact_mod_cast clog
  have lp : 0≤π-maxAngle S := by
    by_contra! neg
    have := mul_neg_of_pos_of_neg (show 0<(j:ℝ)+2 by positivity) neg
    linarith [pi_pos]
  have top : φ≤θ := by nlinarith [mul_le_mul_of_nonneg_right rj lp]
  have same : θ=EuclideanGeometry.angle x p q := (sight p q x).trans (EuclideanGeometry.angle_comm _ _ _)
  have acute := near_angle pq (near x hx)
  have order : sin φ≤sin (EuclideanGeometry.angle x p q) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) acute (top.trans_eq same)
  have law := EuclideanGeometry.law_sin x p q
  have middle : sin φ*dist p q≤dist x q := calc
    _ ≤ sin (EuclideanGeometry.angle x p q)*dist p q := mul_le_mul_of_nonneg_right order dist_nonneg
    _ = sin (EuclideanGeometry.angle q x p)*dist q x := law
    _ ≤ 1*dist q x := mul_le_mul_of_nonneg_right (Real.sin_le_one _) dist_nonneg
    _ = dist x q := by simp [dist_comm]
  exact ⟨x,sub hx,middle.trans (near x hx),middle⟩

/-- Every pair of distinct points in any low-angle competitor has a third point
far from both at the scale of their separation. Apply to a diameter pair to normalize the scale. -/
theorem separated_third {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {j : ℕ} (big : 2^(j+1)<S.card) {φ : ℝ} (ph : 0<φ)
    (budget : π+2*φ≤((j:ℝ)+2)*(π-maxAngle S)) :
    ∃ x∈S, sin φ*dist p q≤dist x p ∧ sin φ*dist p q≤dist x q := by
  classical
  let P:=S.filter (fun x=>dist x p≤dist x q)
  let Q:=S.filter (fun x=>dist x q≤dist x p)
  have cover : S⊆P∪Q := by
    intro x hx
    rcases le_total (dist x p) (dist x q) with h|h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,h⟩)
  have cap := (Finset.card_le_card cover).trans (Finset.card_union_le P Q)
  rw [pow_succ] at big
  by_cases h : 2^j<Q.card
  · have ext : p∉Q := by simp [Q,hp,pq]
    exact cell_witness (Finset.filter_subset _ _) hp pq ext (fun _ h=>(Finset.mem_filter.mp h).2) h ph budget
  · have large : 2^j<P.card := by omega
    have ext : q∉P := by simp [P,hq,pq.symm]
    obtain ⟨x,hx,first,second⟩:=cell_witness (Finset.filter_subset _ _) hq pq.symm ext
      (fun _ h=>(Finset.mem_filter.mp h).2) large ph budget
    rw [dist_comm q p] at first second
    exact ⟨x,hx,second,first⟩

theorem nine_metric {S : Finset Point} (nine : 9≤S.card) (ang : maxAngle S≤5*π/7)
    {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q) :
    ∃ x∈S, sin (π/14)*dist p q≤dist x p ∧ sin (π/14)*dist p q≤dist x q := by
  apply separated_third (j:=2) hp hq pq (by norm_num;omega) (by positivity)
  push_cast
  linarith

end R51.Metric
#print axioms R51.Metric.separated_third
#print axioms R51.Metric.nine_metric
