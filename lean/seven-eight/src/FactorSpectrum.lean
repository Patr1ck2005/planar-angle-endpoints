import FactorPacking

noncomputable section
namespace R49.FactorPacking
open Real JSP404 R49.ChordBins R37.SignedFan InnerProductGeometry
variable {F : Finset Point} {n : ℕ}

def spectrum (C : Chart F n) : Finset ℝ :=
  Finset.univ.biUnion (fun a : F => ((Finset.univ.erase a).image (C.bearing a)))

theorem mem_spectrum (C : Chart F n) {x : ℝ} :
    x∈spectrum C ↔ ∃ a b : F, a≠b ∧ C.bearing a b=x := by
  classical
  simp [spectrum,ne_comm]

def sign (C : Chart F n) (a b : F) := C.label a (C.slot a b)
theorem signs_opposite (C : Chart F n) (a b : F) (ne : a≠b) : sign C a b ≠ sign C b a := by
  unfold sign
  rw [←C.same_slot a b]
  exact C.separates _ _ ne

abbrev Legal (F : Finset Point) (l : ℝ) := ∀ a∈F, ∀ b∈F, ∀ c∈F, a≠b → a≠c → b≠c →
  EuclideanGeometry.angle a b c≤π-l

private theorem observed (C : Chart F n) {l t : ℝ} (ok : Legal F l) {a b c : F} (ab : a≠b) (ac : a≠c)
    (close : |lifted t (C.bearing a b)-lifted t (C.bearing a c)|<l) :
    signAt t (C.bearing a b) (sign C a b)=signAt t (C.bearing a c) (sign C a c) := by
  by_cases e : b=c
  · rw [e]
  have pt {x y : F} (h : x≠y) : (x:Point)≠y := fun eq => h (Subtype.ext eq)
  have law := ok b b.property a a.property c c.property (pt ab.symm) (pt e) (pt ac)
  obtain ⟨r,rp,rb⟩ := C.realized _ _ ab
  obtain ⟨s,sp,sc⟩ := C.realized _ _ ac
  change angle ((b:Point)-a) ((c:Point)-a)≤_ at law
  rw [rb,sc,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,
    angle_oriented (C.range _ _) (C.range _ _)] at law
  change (if sign C a b=sign C a c then _ else _)≤_ at law
  have range : |C.bearing a b-C.bearing a c|≤π := abs_le.mpr ⟨by linarith [(C.range a b).1,(C.range a c).2],
    by linarith [(C.range a b).2,(C.range a c).1]⟩
  rw [lift_diff range] at close
  cases sb : sign C a b <;> cases sd : sign C a c <;> by_cases hb : C.bearing a b<t <;>
    by_cases hc : C.bearing a c<t <;> simp [signAt,hb,hc] <;> simp [sb,sd,hb,hc] at close law <;> linarith

theorem selected (C : Chart F n) {l t : ℝ} (lp : 0<l) (ok : Legal F l)
    (cut : ∀ a∈spectrum C, Apart l t a) :
    ∃ P : Finset ℝ, P⊆spectrum C ∧ Nat.clog 2 F.card≤P.card ∧
      ∀ a∈P, ∀ b∈P, a≠b → Apart l a b := by
  classical
  obtain ⟨P,sub,cover,sep⟩ := greedy (spectrum C) (lifted t) lp
  let V (a b : F) (j : P) := a≠b ∧ lifted t j≤lifted t (C.bearing a b) ∧
    lifted t (C.bearing a b)<lifted t j+l
  let bit (a : F) (j : P) := if h : ∃ b, V a b j then signAt t (C.bearing a h.choose) (sign C a h.choose) else false
  have known {a b : F} {j : P} (vis : V a b j) : bit a j=signAt t (C.bearing a b) (sign C a b) := by
    have ex : ∃ z, V a z j := ⟨b,vis⟩
    change (if h : ∃ z, V a z j then _ else _) = _
    rw [dif_pos ex]
    exact observed C ok ex.choose_spec.1 vis.1 (abs_lt.mpr ⟨by linarith [vis.2.2,ex.choose_spec.2.1],
      by linarith [vis.2.1,ex.choose_spec.2.2]⟩)
  have inj : Function.Injective bit := by
    intro a b eq
    by_contra ne
    obtain ⟨j,hj,lo,hi⟩ := cover (C.bearing a b) ((mem_spectrum C).mpr ⟨a,b,ne,rfl⟩)
    let k : P := ⟨j,hj⟩
    have va : V a b k := ⟨ne,lo,hi⟩
    have vb : V b a k := by
      refine ⟨Ne.symm ne,?_,?_⟩
      · simpa only [C.same_bearing b a] using lo
      · simpa only [C.same_bearing b a] using hi
    have same := congrFun eq k
    rw [known va,known vb,C.same_bearing b a] at same
    have diff := signs_opposite C a b ne
    unfold signAt at same
    split_ifs at same <;> simp_all
  have hc := Fintype.card_le_of_injective bit inj
  have count : F.card≤2^P.card := by simpa [Fintype.card_fun] using hc
  refine ⟨P,sub,Nat.clog_le_of_le_pow count,?_⟩
  intro a ha b hb ne
  obtain ⟨u,v,_,ra⟩ := (mem_spectrum C).mp (sub ha)
  obtain ⟨p,q,_,rb⟩ := (mem_spectrum C).mp (sub hb)
  have bounds : |a-b|≤π := abs_le.mpr ⟨by linarith [(C.range u v).1,(C.range p q).2],
    by linarith [(C.range u v).2,(C.range p q).1]⟩
  exact unlift bounds (cut _ (sub ha)) (cut _ (sub hb)) lp (sep _ ha _ hb ne)

end R49.FactorPacking
#print axioms R49.FactorPacking.selected
