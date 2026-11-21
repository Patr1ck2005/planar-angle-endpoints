import DistinctPhysicalAxes
import InteriorThree

noncomputable section
namespace R93.Interior
open JSP404 Real InnerProductGeometry R55.WeightedCollision R56.Decorated R92.Tight

/-- Combining one unchanged physical microscopic kit with the displayed
three actual chords gives projective separation on their disjoint union. -/
theorem actual_completion {I : Type*} {c : I→Point} (ci : Function.Injective c)
    {δ : ℝ} {D : I→ℕ} (A : Axes c D (π-δ)) (i : I) (h : Fin 3↪I) (off : ∀j,h j≠i)
    (legal : ∀j k,j≠k→δ≤EuclideanGeometry.angle (c (h j)) (c i) (c (h k)) ∧
      EuclideanGeometry.angle (c (h j)) (c i) (c (h k))≤π-δ) :
    Packed δ (Sum.elim (A.v i) (fun j=>c (h j)-c i)) := by
  constructor
  · intro p
    cases p with
    | inl j => exact A.nonzero i j
    | inr j => exact sub_ne_zero.mpr (ci.ne (off j))
  · intro p q ne r sign
    cases p with
    | inl a =>
      cases q with
      | inl b => simpa using A.internal i a b (fun e=>ne (congrArg Sum.inl e)) r 1 sign (Or.inr rfl)
      | inr b => exact A.outside i (h b) (off b).symm a r sign
    | inr a =>
      cases q with
      | inl b =>
        have plus:=A.outside i (h a) (off a).symm b r sign
        rcases sign with rfl|rfl
        · change angle ((-1:ℝ) • (c (h a)-c i)) (A.v i b)≤π-δ
          simp only [neg_one_smul,angle_neg_left] at plus ⊢
          rwa [angle_comm]
        · change angle ((1:ℝ) • (c (h a)-c i)) (A.v i b)≤π-δ
          simp only [one_smul] at plus ⊢
          rwa [angle_comm]
      | inr b =>
        obtain ⟨lo,hi⟩:=legal a b (fun e=>ne (congrArg Sum.inr e))
        change δ≤angle (c (h a)-c i) (c (h b)-c i) at lo
        rcases sign with rfl|rfl
        · simp only [Sum.elim_inr,neg_one_smul,angle_neg_left];linarith
        · change angle (c (h a)-c i) (c (h b)-c i)≤π-δ at hi
          simpa only [Sum.elim_inr,one_smul] using hi

/-- When a surrounded site has at least one microscopic axis at the
tight reserve, the whole support consists of that site and exactly three others. -/
theorem cardinal_of_tight_axes {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {i : I} (inside : c i∈convexHull ℝ (c '' {j | j≠i})) {δ : ℝ} (dp : 0<δ)
    (mac : Macro c (π-δ)) {D : I→ℕ} (A : Axes c D (π-δ)) (positive : 0<D i)
    (tight : ((D i:ℝ)+3)*δ=π) : Fintype.card I=4 := by
  classical
  let O:={a : I // a≠i}
  let x (a : O):=c a.val-c i
  have ex:=convexHull_nonempty_iff.mp (show (convexHull ℝ (c '' {a | a≠i})).Nonempty from ⟨_,inside⟩)
  obtain ⟨_,j,ji,rfl⟩:=ex
  obtain ⟨h,_,off,_⟩:=anchored_embedding ci ji inside dp mac
  let e : Fin 3↪O:=⟨fun a=>⟨h a,off a⟩,fun a b eq=>h.injective (congrArg Subtype.val eq)⟩
  have many : 3≤Fintype.card O:=by simpa using Fintype.card_le_of_injective e e.injective
  have dif (a b : O) (ne : a≠b) : ¬SameAxis (x a) (x b):=
    different_axes ci (by linarith : π-δ<π) mac a.property b.property (fun eq=>ne (Subtype.ext eq))
  have cover (a : O) : ∃C : Fin 3→Point,Packed δ (Sum.elim (A.v i) C) ∧ ∃j,C j=x a := by
    obtain ⟨f,first,out,legal⟩:=anchored_embedding ci a.property inside dp mac
    exact ⟨fun j=>c (f j)-c i,actual_completion ci A i f out legal,0,by simp [x,first]⟩
  have few:=candidate_count positive dp tight (A.v i) x dif cover
  have all : Fintype.card O=Fintype.card I-1:=by simp [O,Fintype.card_subtype_compl]
  omega

/-- Rigidity at the attainable lower endpoint of a surrounded positive
fiber with at least two points. No generic-position or optimality assumption. -/
theorem endpoint_card_four {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀j,0<w j) (i : I) (big : 2≤w i)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i}))
    (hit : π-π/((Nat.clog 2 (w i):ℝ)+3)∈attainable w c) : Fintype.card I=4 := by
  classical
  have ex:=convexHull_nonempty_iff.mp (show (convexHull ℝ (c '' {j | j≠i})).Nonempty from ⟨_,inside⟩)
  obtain ⟨_,j,ji,rfl⟩:=ex
  let : Nontrivial I:=⟨j,i,ji⟩
  let δ:=π/((dim w i:ℝ)+3)
  have den : 0<(dim w i:ℝ)+3:=by positivity
  have dp : 0<δ:=div_pos pi_pos den
  have dpos : 0<dim w i:=Nat.clog_pos (by decide) (by omega)
  have tight : ((dim w i:ℝ)+3)*δ=π:=by dsimp [δ];field_simp
  change π-δ∈attainable w c at hit
  obtain ⟨_,mac,v,unit,inter,out⟩:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  let A : Axes c (dim w) (π-δ):=⟨v,fun j a zero=>by simpa [zero] using unit j a,inter,out⟩
  exact cardinal_of_tight_axes ci inside dp mac A dpos tight

end R93.Interior
#print axioms R93.Interior.actual_completion
#print axioms R93.Interior.cardinal_of_tight_axes
#print axioms R93.Interior.endpoint_card_four
