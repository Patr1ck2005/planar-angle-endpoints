import AnchorPacking

noncomputable section
namespace R51.Anchored
open Real JSP404 R49.ChordBins R49.FactorPacking R37.SignedFan InnerProductGeometry

/-- A cloud as seen from its external anchor. The vector v points from the cloud towards p. -/
def InCone (F : Finset Point) (p v : Point) (η : ℝ) := ∀ x∈F, angle v (p-x)≤η

theorem signed_polar {v : Point} (nv : v≠0) : ∃ t : ℝ, ∃ b : Bool,
    ∃ r : ℝ, (0≤t ∧ t<π) ∧ 0<r ∧ v=r • oriented t b := by
  obtain ⟨row,rep,_⟩ := exists_row (fun _ : Unit => v) pi_pos (fun _ => nv)
    (by intro _ _; simp [angle_self nv])
  obtain ⟨j,r,hr,eq⟩ := rep.1 ()
  exact ⟨_,_,r,row.bounds j,hr,eq⟩

/-- Each observed anchor direction forbids an arc around its projective axis. -/
theorem cone_cut {S F : Finset Point} {n : ℕ} (C : Chart F n) (sub : F⊆S)
    {p : Point} (ps : p∈S) (ext : p∉F) {v : Point} {t r : ℝ} {b : Bool}
    (ht : 0≤t ∧ t<π) (hr : 0<r) (eq : v=r • oriented t b)
    {η : ℝ} (cone : InCone F p v η) (a : ℝ) (ha : a∈spectrum C) :
    Apart (π-maxAngle S-η) t a := by
  have side (x y : F) (ne : x≠y) : angle v ((y:Point)-x)≤maxAngle S+η := by
    have px : p≠(x:Point) := fun e => ext (e ▸ x.property)
    have py : p≠(y:Point) := fun e => ext (e ▸ y.property)
    have xy : (x:Point)≠(y:Point) := fun e => ne (Subtype.ext e)
    have h:=angle_le_maxAngle ps (sub x.property) (sub y.property) px py xy
    change angle (p-(x:Point)) ((y:Point)-x)≤_ at h
    linarith [angle_le_angle_add_angle v (p-(x:Point)) ((y:Point)-x),cone x x.property]
  obtain ⟨x,y,xy,rfl⟩ := (mem_spectrum _).mp ha
  have h := side x y xy
  have z := side y x xy.symm
  rw [←neg_sub (y:Point) (x:Point),angle_neg_right] at z
  obtain ⟨s,hs,ys⟩ := C.realized x y xy
  rw [eq,ys,angle_smul_left_of_pos _ _ hr,angle_smul_right_of_pos _ _ hs,
    angle_oriented ht (C.range _ _)] at h z
  split_ifs at h z <;> exact ⟨by linarith,by linarith⟩

/-- A cloud of any shape and one external point. The error 2η is paid once across the two ends
of the interval of permitted chord directions, independently of the cloud cardinality. -/
theorem anchored_budget {S F : Finset Point} (sub : F⊆S) (two : 2≤F.card)
    {p v : Point} (ps : p∈S) (ext : p∉F) (nv : v≠0)
    {η : ℝ} (pos : 0≤η) (cone : InCone F p v η) :
    ((Nat.clog 2 F.card : ℝ)+1)*(π-maxAngle S)≤π+2*η := by
  classical
  let l := π-maxAngle S
  by_cases lp : 0<l
  · have lim : l≤π := by dsimp [l];linarith [maxAngle_nonneg S]
    have legal : Legal F l := by
      intro a ha b hb c hc ab ac bc
      dsimp [l]; simpa using angle_le_maxAngle (sub ha) (sub hb) (sub hc) ab ac bc
    obtain ⟨n,hn⟩ := exists_nat_gt (π/l)
    have np : (0:ℝ)<n := (div_pos pi_pos lp).trans hn
    have margin : π/(n:ℝ)<l := (div_lt_iff₀ np).mpr (by linarith [(div_lt_iff₀ lp).mp hn])
    let C : Chart F n := Classical.choice (planar two (by exact_mod_cast np : 0<n) margin lim legal)
    obtain ⟨t,b,r,ht,hr,eq⟩ := signed_polar nv
    have cut := cone_cut C sub ps ext ht hr eq cone
    have h:=line_budget C two lp legal cut
    change ((Nat.clog 2 F.card:ℝ)+1)*l≤_
    linarith
  · have neg : l≤0 := le_of_not_gt lp
    have factor : 0≤(Nat.clog 2 F.card:ℝ)+1 := by positivity
    exact (mul_nonpos_of_nonneg_of_nonpos factor neg).trans (by linarith [pi_pos])

/-- In particular a cloud of at least five points in a nine-point competitor with maximum
angle at most 5π/7 + ε cannot fit into a viewing cone of half-aperture below π/14 − 2ε. -/
theorem five_point_aperture {S F : Finset Point} (sub : F⊆S) (five : 5≤F.card)
    {p v : Point} (ps : p∈S) (ext : p∉F) (nv : v≠0)
    {η ε : ℝ} (pos : 0≤η) (cone : InCone F p v η) (near : maxAngle S≤5*π/7+ε) :
    π/14-2*ε≤η := by
  have cnt : 3≤Nat.clog 2 F.card := by
    by_contra! h
    have h' : Nat.clog 2 F.card≤2 := by omega
    have := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp h'
    norm_num at this
    omega
  have k : (3:ℝ)≤Nat.clog 2 F.card := by exact_mod_cast cnt
  have bound:=anchored_budget sub (by omega) ps ext nv pos cone
  by_cases h : 0≤π-maxAngle S
  · nlinarith [mul_le_mul_of_nonneg_right k h]
  · linarith [pi_pos]

end R51.Anchored
#print axioms R51.Anchored.anchored_budget
#print axioms R51.Anchored.five_point_aperture
