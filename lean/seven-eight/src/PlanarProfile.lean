import RowBands

namespace R37.SignedFan
open Real InnerProductGeometry JSP404

/-- The geometric even-band restriction for a pair of actual vectors
represented in the row, with no chart bearings in the conclusion. -/
theorem Row.represented_angle_band {I : Type*} (F : Row) (x : I → Point)
    {lam : ℝ} (hl : 0<lam) (rep : F.Represents x) (h : F.Legal lam) (i j : I) :
    FullSwitchTriangle.Band F.switches (π/lam) (angle (x i) (x j)/lam) := by
  obtain ⟨p,r,hr,hi⟩ := rep.1 i
  obtain ⟨q,s,hs,hj⟩ := rep.1 j
  rw [hi,hj,angle_smul_left_of_pos _ _ hr,angle_smul_right_of_pos _ _ hs]
  exact F.angle_band hl h p q

/-- This profile is produced for every finite set. Each row records the
actual normalized rays to all other points. -/
def IsProfile (S : Finset Point) (lam : ℝ) (F : S → Row) : Prop :=
  ∀ p, (F p).Represents (fun q : S.erase p.val => (q:Point)-p.val) ∧ (F p).Legal lam

theorem profile_angle_band (S : Finset Point) {lam : ℝ} (hl : 0<lam) (F : S → Row)
    (h : IsProfile S lam F) (a b c : S) (hab : a≠b) (hcb : c≠b) :
    FullSwitchTriangle.Band (F b).switches (π/lam)
      (EuclideanGeometry.angle (a:Point) (b:Point) (c:Point)/lam) := by
  have make (p : S) (hp : p≠b) : p.val∈S.erase b.val := Finset.mem_erase.mpr
    ⟨fun e => hp (Subtype.ext e),p.property⟩
  exact (F b).represented_angle_band _ hl (h b).1 (h b).2 ⟨a,make a hab⟩ ⟨c,make c hcb⟩

/-- In any realized profile on a genuine point set, at most two rows
can reach odd switch count m in the lower half of its strip. -/
theorem at_most_two_top (S : Finset Point) {lam : ℝ} (hl : 0<lam) (F : S → Row)
    (h : IsProfile S lam F) (m : ℕ) (hm : m%2=1) (width : π/lam-(m:ℝ)<1/2) :
    (Finset.univ.filter (fun p : S => (F p).switches=m)).card≤2 := by
  classical
  by_contra! many
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp many
  have ea := (Finset.mem_filter.mp ha).2
  have eb := (Finset.mem_filter.mp hb).2
  have ec := (Finset.mem_filter.mp hc).2
  have ab := profile_angle_band S hl F h a b c hab hbc.symm
  have bc := profile_angle_band S hl F h b c a hbc hac
  have ca := profile_angle_band S hl F h c a b hac.symm hab.symm
  rw [eb] at ab
  rw [ec] at bc
  rw [ea] at ca
  have ba : (b:Point)≠a := fun e => hab (Subtype.ext e.symm)
  have eq := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c:Point) ba
  apply FullSwitchTriangle.no_triangle hm width ?_ ab bc ca
  rw [←add_div,←add_div,eq]

/-- End-to-end Euclidean row theorem: existence, representation, oddity,
whole-row budget, actual angle bands, and at most two top rows. Only
point-set cardinality, the scale and ordinary triangle legality are inputs. -/
theorem planar_switch_profile (S : Finset Point) (hs : 2≤S.card) {lam : ℝ}
    (hl : 0<lam) (hπ : lam≤π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
        EuclideanGeometry.angle a b c≤π-lam) :
    ∃ F : S → Row, IsProfile S lam F ∧
      (∀ p, (F p).switches%2=1 ∧ ((F p).switches:ℝ)*lam≤π) ∧
      (∀ a b c, a≠b → c≠b → FullSwitchTriangle.Band (F b).switches (π/lam)
        (EuclideanGeometry.angle (a:Point) (b:Point) (c:Point)/lam)) ∧
      ∀ m : ℕ, m%2=1 → π/lam-(m:ℝ)<1/2 →
        (Finset.univ.filter (fun p : S => (F p).switches=m)).card≤2 := by
  classical
  choose F hr hL using fun p : S => exists_planar_row S p p.property hs hl hπ legal
  have hp : IsProfile S lam F := fun p => ⟨hr p,hL p⟩
  exact ⟨F,hp,fun p => ⟨(F p).switches_odd,(F p).total_budget (hL p)⟩,
    profile_angle_band S hl F hp,at_most_two_top S hl F hp⟩

#print axioms at_most_two_top
#print axioms planar_switch_profile
end R37.SignedFan
