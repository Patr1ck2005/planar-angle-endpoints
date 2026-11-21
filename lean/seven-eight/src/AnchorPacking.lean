import FactorSpectrum
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

noncomputable section
namespace R51.Anchored
open Real JSP404 R49.ChordBins R49.FactorPacking R37.SignedFan InnerProductGeometry
variable {F : Finset Point} {n : ℕ}

/- The observed-sign argument and interval span specialize the proofs in R49 FactorSpectrum
and FactorPacking. Here the cut margin is independent of the internal separation. -/
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

theorem selectedLine (C : Chart F n) {l : ℝ} (t : ℝ) (lp : 0<l) (ok : Legal F l) :
    ∃ P : Finset ℝ, P⊆spectrum C ∧ Nat.clog 2 F.card≤P.card ∧
      ∀ a∈P, ∀ b∈P, a≠b → l≤|lifted t a-lifted t b| := by
  classical
  obtain ⟨P,sub,cover,sep⟩ := greedy (spectrum C) (lifted t) lp
  let V (a b : F) (j : P) := a≠b ∧ lifted t j≤lifted t (C.bearing a b) ∧
    lifted t (C.bearing a b)<lifted t j+l
  let bit (a : F) (j : P) := if h : ∃ b, V a b j then signAt t (C.bearing a h.choose) (sign C a h.choose) else false
  have known {a b : F} {j : P} (vis : V a b j) : bit a j=signAt t (C.bearing a b) (sign C a b) := by
    have ex : ∃ z, V a z j := ⟨b,vis⟩
    change (if h : ∃ z, V a z j then _ else _) = _
    rw [dite_eq_left ex]
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
  exact ⟨P,sub,Nat.clog_le_of_le_pow count,sep⟩

theorem interval_span (D : Finset ℝ) {l : ℝ} (lp : 0<l) (ne : D.Nonempty) (lo hi : ℝ)
    (bounds : ∀ x∈D, lo≤x ∧ x≤hi)
    (sep : ∀ a∈D, ∀ b∈D, a≠b → l≤|a-b|) : (D.card:ℝ)*l≤hi-lo+l := by
  classical
  induction D using Finset.strongInductionOn generalizing lo with
  | _ D ih =>
    let a := D.min' ne
    have ha : a∈D := D.min'_mem _
    have drop := Finset.erase_ssubset ha
    have size := Finset.card_erase_add_one ha
    have eq : ((D.erase a).card:ℝ)+1=D.card := by exact_mod_cast size
    rcases (D.erase a).eq_empty_or_nonempty with empty|non
    · rw [empty] at eq; simp only [Finset.card_empty,Nat.cast_zero,zero_add] at eq
      nlinarith [(bounds a ha).1,(bounds a ha).2]
    · have next := ih (D.erase a) drop non (a+l) (fun x hx => by
        have mem := (Finset.mem_erase.mp hx).2
        have apart := sep x mem a ha (Finset.mem_erase.mp hx).1
        rw [abs_of_nonneg (sub_nonneg.mpr (D.min'_le _ mem))] at apart
        exact ⟨by linarith,(bounds x mem).2⟩)
        (fun x hx y hy h => sep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) h)
      nlinarith [(bounds a ha).1]


/-- The internal code retains its full separation even when an external direction has slack. -/
theorem line_budget (C : Chart F n) (two : 2≤F.card) {l t g : ℝ} (lp : 0<l)
    (ok : Legal F l) (cut : ∀ a∈spectrum C, Apart g t a) :
    ((Nat.clog 2 F.card : ℝ)-1)*l+2*g≤π := by
  classical
  obtain ⟨P,sub,count,sep⟩ := selectedLine C t lp ok
  have cn : 0<Nat.clog 2 F.card := Nat.clog_pos (by decide) (by omega)
  have pn := Finset.card_pos.mp (lt_of_lt_of_le cn count)
  let Q := P.image (lifted t)
  have unique : Set.InjOn (lifted t) (↑P:Set ℝ) := by
    intro a ha b hb eq
    by_contra ne
    have h:=sep a ha b hb ne
    rw [eq,sub_self,abs_zero] at h
    linarith
  have card : Q.card=P.card := Finset.card_image_of_injOn unique
  have bound := interval_span Q lp (pn.image _) (t+g) (t+π-g) (by
    intro x hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    exact safe_lift (cut _ (sub ha))) (by
    intro x hx y hy ne
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hy
    exact sep _ ha _ hb (fun eq => ne (congrArg _ eq)))
  rw [card] at bound
  have rcount : (Nat.clog 2 F.card : ℝ)≤P.card := by exact_mod_cast count
  nlinarith [mul_le_mul_of_nonneg_right rcount lp.le]

end R51.Anchored
#print axioms R51.Anchored.line_budget
