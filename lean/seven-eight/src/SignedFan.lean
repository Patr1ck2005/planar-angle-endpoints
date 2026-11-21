import JSP404.EquallySpacedDirections
import Mathlib.Data.Finset.Sort

/-! Realize a finite fan of actual rays as signed distinct projective
bearings, in increasing order in [0,π). Counts and gap geometry include
the compulsory sign reversal on crossing the projective seam. -/

namespace R37.SignedFan
open Real InnerProductGeometry JSP404
open scoped BigOperators

noncomputable def oriented (u : ℝ) (b : Bool) : Point :=
  if b then circleDirection u else -circleDirection u

private theorem polar {x : Point} (hx : x≠0) :
    ∃ u : ℝ, ∃ b : Bool, ∃ r : ℝ, (0≤u ∧ u<π) ∧ 0<r ∧ x=r • oriented u b := by
  have upper (y : Point) (hn : y≠0) (hy : 0≤y 1) :
      ∃ u : ℝ, ∃ b : Bool, ∃ r : ℝ, (0≤u ∧ u<π) ∧ 0<r ∧ y=r • oriented u b := by
    obtain ⟨r,u,hr,hu,hπ,he⟩ := exists_polar_of_second_nonneg hn hy
    rcases lt_or_eq_of_le hπ with h | rfl
    · exact ⟨u,true,r,⟨hu,h⟩,hr,by simpa [oriented] using he⟩
    · exact ⟨0,false,r,⟨le_rfl,pi_pos⟩,hr,by simpa [oriented,circleDirection_pi] using he⟩
  by_cases h : 0≤x 1
  · exact upper x hx h
  · obtain ⟨u,b,r,hu,hr,he⟩ := upper (-x) (by simpa) (by simpa using le_of_not_ge h)
    refine ⟨u,!b,r,hu,hr,?_⟩
    have eq := congrArg Neg.neg he
    cases b <;> simpa [oriented,smul_neg] using eq

theorem angle_oriented {u v : ℝ} (hu : 0≤u ∧ u<π) (hv : 0≤v ∧ v<π) (a b : Bool) :
    angle (oriented u a) (oriented v b) = if a=b then |u-v| else π-|u-v| := by
  have h : angle (circleDirection u) (circleDirection v) = |u-v| := by
    rw [angle_circleDirection,←cos_abs (u-v),arccos_cos (abs_nonneg _)]
    exact abs_le.mpr ⟨by linarith [hu.1,hv.2],by linarith [hv.1,hu.2]⟩
  cases a <;> cases b <;> simp [oriented,angle_neg_left,angle_neg_right,h]

structure Row where
  n : ℕ
  bearing : Fin (n+1) → ℝ
  sign : Fin (n+1) → Bool
  sorted : StrictMono bearing
  bounds : ∀ j, 0≤bearing j ∧ bearing j<π

def Row.Represents {I : Type*} (F : Row) (x : I → Point) : Prop :=
  (∀ i, ∃ j, ∃ r : ℝ, 0<r ∧ x i=r • oriented (F.bearing j) (F.sign j)) ∧
  (∀ j, ∃ i, ∃ r : ℝ, 0<r ∧ x i=r • oriented (F.bearing j) (F.sign j))

def Row.Legal (F : Row) (lam : ℝ) : Prop :=
  ∀ i j, angle (oriented (F.bearing i) (F.sign i)) (oriented (F.bearing j) (F.sign j)) ≤ π-lam

/-- Construction from actual nonzero rays. Duplicate projective directions
are combined only after local legality proves their signed rays agree. -/
theorem exists_row {I : Type*} [Fintype I] [Nonempty I] (x : I → Point) {lam : ℝ}
    (hl : 0<lam) (hn : ∀ i, x i≠0)
    (ha : ∀ i j, angle (x i) (x j)≤π-lam) :
    ∃ F : Row, F.Represents x ∧ F.Legal lam := by
  classical
  choose u b r hu hr hx using fun i => polar (hn i)
  let S := Finset.univ.image u
  have hcard : 0<S.card := Finset.card_pos.mpr
    ⟨u (Classical.arbitrary I),Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let n := S.card-1
  have eqcard : S.card=n+1 := by dsimp [n]; omega
  let e := S.orderIsoOfFin eqcard
  have pre (z : S) : ∃ i, u i=z.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp z.property
    exact ⟨i,hi⟩
  let rep (j : Fin (n+1)) : I := (pre (e j)).choose
  have hrep (j : Fin (n+1)) : u (rep j)=(e j).val := (pre _).choose_spec
  have uniq {i j : I} (eij : u i=u j) : b i=b j := by
    by_contra h
    have h' := ha i j
    rw [hx i,hx j,angle_smul_left_of_pos _ _ (hr i),angle_smul_right_of_pos _ _ (hr j),
      angle_oriented (hu i) (hu j),if_neg h,eij,sub_self,abs_zero,sub_zero] at h'
    linarith
  let F : Row := ⟨n,fun j => (e j).val,fun j => b (rep j),
    fun i j hij => e.strictMono hij,fun j => by rw [←hrep j]; exact hu (rep j)⟩
  refine ⟨F,⟨?_,?_⟩,?_⟩
  · intro i
    let z : S := ⟨u i,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    let j := e.symm z
    have ej : (e j).val=u i := congrArg Subtype.val (e.apply_symm_apply z)
    have sb := uniq ((hrep j).trans ej)
    exact ⟨j,r i,hr i,by change x i=r i • oriented (e j).val (b (rep j)); rw [ej,sb]; exact hx i⟩
  · intro j
    exact ⟨rep j,r (rep j),hr _,by change x (rep j)=_ • oriented (e j).val _; rw [←hrep j]; exact hx _⟩
  · intro i j
    have h := ha (rep i) (rep j)
    rw [hx _,hx _,angle_smul_left_of_pos _ _ (hr _),angle_smul_right_of_pos _ _ (hr _),hrep i,hrep j] at h
    exact h

/-- In the original finite plane configuration, every basepoint with a
neighbor obtains a genuinely realized signed direction row. -/
theorem exists_planar_row (S : Finset Point) (p : Point) (hp : p∈S)
    (hs : 2≤S.card) {lam : ℝ} (hl : 0<lam) (hπ : lam≤π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
        EuclideanGeometry.angle a b c≤π-lam) :
    ∃ F : Row, F.Represents (fun q : S.erase p => (q:Point)-p) ∧ F.Legal lam := by
  classical
  have hcnt := Finset.card_erase_of_mem hp
  have pos : 0<(S.erase p).card := by omega
  have : Nonempty (S.erase p) := (Finset.card_pos.mp pos).to_subtype
  have hn (q : S.erase p) : (q:Point)≠p := (Finset.mem_erase.mp q.property).1
  apply exists_row _ hl (fun q => sub_ne_zero.mpr (hn q))
  intro i j
  by_cases he : i=j
  · subst j
    rw [angle_self (sub_ne_zero.mpr (hn i))]
    linarith
  · exact legal i (Finset.mem_of_mem_erase i.property) p hp j (Finset.mem_of_mem_erase j.property)
      (hn i) (fun e => he (Subtype.ext e)) (hn j).symm

#print axioms exists_planar_row
end R37.SignedFan
