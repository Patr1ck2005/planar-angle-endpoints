import TwoCutPacking

noncomputable section
namespace R52.TwoAnchor
open Real JSP404 R49.ChordBins R49.FactorPacking R51.Anchored R37.SignedFan InnerProductGeometry

abbrev defect (S : Finset Point) := π-maxAngle S
abbrev bits (F : Finset Point) : ℝ := Nat.clog 2 F.card

structure Corner (S : Finset Point) (a b c : Point) where
  points : Finset Point
  sub : points⊆S
  middle : a∈points
  left : b∈S
  right : c∈S
  outsideL : b∉points
  outsideR : c∉points
  ends : b≠c
  eL : ℝ
  eR : ℝ
  posL : 0≤eL
  posR : 0≤eR
  coneL : InCone points b (b-a) eL
  coneR : InCone points c (c-a) eR

abbrev Corner.error {S : Finset Point} {a b c : Point} (A : Corner S a b c) := A.eL+A.eR

theorem corner {S : Finset Point} {a b c : Point} (A : Corner S a b c) (two : 2≤A.points.card) :
    (bits A.points+2)*defect S≤π+2*A.error ∨
      EuclideanGeometry.angle b a c≤π-(bits A.points+1)*defect S+A.error := by
  classical
  let l := defect S
  let θ := EuclideanGeometry.angle b a c
  have ab : a≠b := fun eq => A.outsideL (eq ▸ A.middle)
  have ac : a≠c := fun eq => A.outsideR (eq ▸ A.middle)
  have ea : 0≤A.error := add_nonneg A.posL A.posR
  have tcap : θ≤π-l := by
    dsimp [θ,l,defect];simpa using angle_le_maxAngle A.left (A.sub A.middle) A.right ab.symm A.ends ac
  by_cases lp : 0<l
  · have leg : Legal A.points l := by
      intro x hx y hy z hz xy xz yz
      dsimp [l,defect];simpa using angle_le_maxAngle (A.sub hx) (A.sub hy) (A.sub hz) xy xz yz
    obtain ⟨n,hn⟩ := exists_nat_gt (π/l)
    have np : 0<(n:ℝ) := (div_pos pi_pos lp).trans hn
    have width : π/(n:ℝ)<l := (div_lt_iff₀ np).mpr (by linarith [(div_lt_iff₀ lp).mp hn])
    obtain ⟨C⟩ := planar two (by exact_mod_cast np : 0<n) width (by dsimp [l,defect];linarith [maxAngle_nonneg S]) leg
    obtain ⟨u,bu,r,hu,hr,eq⟩ := signed_polar (sub_ne_zero.mpr ab.symm)
    obtain ⟨v,bv,s,hv,hs,sg⟩ := signed_polar (sub_ne_zero.mpr ac.symm)
    have x := cone_cut C A.sub A.left A.outsideL hu hr eq A.coneL
    have y := cone_cut C A.sub A.right A.outsideR hv hs sg A.coneR
    have h := two_cuts C two lp leg hv x y
    have ang : θ=if bu=bv then |u-v| else π-|u-v| := by
      change angle (b-a) (c-a)=_
      rw [eq,sg,angle_smul_left_of_pos _ _ hr,angle_smul_right_of_pos _ _ hs,angle_oriented hu hv]
    have same : max |u-v| (π-|u-v|)=max θ (π-θ) := by
      rw [ang];split_ifs <;> simp [max_comm]
    rw [same] at h
    change (bits A.points+2)*l≤π+2*A.error ∨ θ≤π-(bits A.points+1)*l+A.error
    change (bits A.points-2)*l+2*(l-A.eL+(l-A.eR))≤π ∨ (bits A.points-1)*l+(l-A.eL+(l-A.eR))≤_ at h
    rcases h with h|h
    · left;dsimp [Corner.error];nlinarith
    · rcases le_max_iff.mp h with h|h
      · left;dsimp [Corner.error] at *;nlinarith
      · right;dsimp [Corner.error];nlinarith
  · left
    change (bits A.points+2)*l≤π+2*A.error
    have p : 0≤bits A.points+2 := by unfold bits;positivity
    linarith [mul_nonpos_of_nonneg_of_nonpos p (le_of_not_gt lp),pi_pos]

theorem two_corners {S : Finset Point} {a b c : Point} (A : Corner S a b c) (B : Corner S b c a)
    (a2 : 2≤A.points.card) (b2 : 2≤B.points.card) :
    (bits A.points+2)*defect S≤π+2*A.error ∨ (bits B.points+2)*defect S≤π+2*B.error ∨
      (bits A.points+bits B.points+3)*defect S≤2*π+A.error+B.error := by
  rcases corner A a2 with h|h
  · exact Or.inl h
  rcases corner B b2 with k|k
  · exact Or.inr (Or.inl k)
  right;right
  have ab : a≠b := fun eq => A.outsideL (eq ▸ A.middle)
  have ac : a≠c := fun eq => A.outsideR (eq ▸ A.middle)
  have other := angle_le_maxAngle (A.sub A.middle) A.right A.left ac ab A.ends.symm
  have sum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi c ab
  dsimp [defect] at *
  nlinarith

theorem three_corners {S : Finset Point} {a b c : Point} (A : Corner S a b c)
    (B : Corner S b c a) (C : Corner S c a b)
    (a2 : 2≤A.points.card) (b2 : 2≤B.points.card) (c2 : 2≤C.points.card) :
    (bits A.points+2)*defect S≤π+2*A.error ∨ (bits B.points+2)*defect S≤π+2*B.error ∨
    (bits C.points+2)*defect S≤π+2*C.error ∨
      (bits A.points+bits B.points+bits C.points+3)*defect S≤2*π+A.error+B.error+C.error := by
  rcases corner A a2 with h|h
  · exact Or.inl h
  rcases corner B b2 with k|k
  · exact Or.inr (Or.inl k)
  rcases corner C c2 with g|g
  · exact Or.inr (Or.inr (Or.inl g))
  right;right;right
  have ab : a≠b := fun eq => A.outsideL (eq ▸ A.middle)
  have sum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi c ab
  dsimp [defect] at *
  nlinarith

end R52.TwoAnchor
#print axioms R52.TwoAnchor.corner
#print axioms R52.TwoAnchor.two_corners
#print axioms R52.TwoAnchor.three_corners
