import CommonDirections
noncomputable section
namespace R66.Common
open Real JSP404 InnerProductGeometry R55.WeightedCollision

private theorem cross {I : Type*} {c : I→Point} {u v : Point} {θ : ℝ} {i : I}
    (nz : u≠0) (U : Visible c u)
    (outside : ∀j,i≠j→∀s:ℝ,(s= -1 ∨ s=1)→angle (s • v) (c j-c i)≤θ)
    (s : ℝ) (sg : s= -1 ∨ s=1) : angle (s • v) u≤θ := by
  obtain ⟨j,t,tn,e⟩:=U i
  have ne : i≠j := by intro eq;subst j;rw [sub_self] at e;exact (smul_ne_zero tn nz) e.symm
  rcases lt_or_gt_of_ne tn with neg|pos
  · have ht : t • u=(-t) • (-u) := by simp
    have bound:=outside j ne (-s) (by rcases sg with rfl|rfl <;> norm_num)
    rw [e,ht,angle_smul_right_of_pos _ _ (neg_pos.mpr neg),neg_smul,angle_neg_neg] at bound
    exact bound
  · simpa only [e,angle_smul_right_of_pos _ _ pos] using outside j ne s sg

private theorem swapSign (u v : Point) (s : ℝ) (sg : s= -1 ∨ s=1) :
    angle (s • u) v=angle (s • v) u := by
  rcases sg with rfl|rfl <;> simp only [one_smul,neg_one_smul,angle_neg_left,angle_comm u v]

/-- Every parallel class represented at every center uses one unit of the
projective angle budget even after all microscopic collision axes are added. -/
theorem common_reserve {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]
    {w : I→ℕ} {c : I→Point} {θ : ℝ} (A : Admissible w c θ) (lt : θ<π)
    (u : J→Point) (nz : ∀j,u j≠0) (ind : ∀j k,j≠k→det (u j) (u k)≠0)
    (vis : ∀j,Visible c (u j)) (i : I) :
    Nat.clog 2 (w i)+Fintype.card J≤⌊π/(π-θ)⌋₊ := by
  obtain ⟨nonneg,mac,v,unit,inter,out⟩:=A
  let f : Fin (dim w i) ⊕ J → Point := Sum.elim (v i) u
  have nzf : ∀j,f j≠0 := by
    rintro (p|p)
    · change v i p≠0
      intro z;have h:=unit i p;simp [z] at h
    · exact nz p
  have legal (j k : Fin (dim w i) ⊕ J) (ne : j≠k) (s : ℝ) (sg : s= -1 ∨ s=1) :
      angle (s • f j) (f k)≤θ := by
    rcases j with j|j <;> rcases k with k|k
    · simpa only [f,Sum.elim_inl,one_smul] using inter i j k (fun e=>ne (congrArg Sum.inl e)) s 1 sg (Or.inr rfl)
    · exact cross (nz k) (vis k) (fun j' n r hr=>out i j' n j r hr) s sg
    · change angle (s • u j) (v i k)≤θ
      rw [swapSign _ _ _ sg]
      exact cross (nz j) (vis j) (fun j' n r hr=>out i j' n k r hr) s sg
    · exact signed_common (ind j k (fun e=>ne (congrArg Sum.inr e))) (vis j) (vis k) mac s sg
  simpa [dim] using signed_budget f nzf (sub_pos.mpr lt) (by linarith : π-θ≤π)
    (by simpa only [sub_sub_cancel] using legal)

/-- A physical all-cardinality lower bound for weighted clusters on a frame
of at most two-to-the-number-of-common-directions distinct macrocenters. -/
theorem common_dyadic {I J : Type*} [Fintype I] [Nontrivial I] [Fintype J]
    {c : I→Point} (inj : Function.Injective c) (u : J→Point) (nz : ∀j,u j≠0)
    (ind : ∀j k,j≠k→det (u j) (u k)≠0) (vis : ∀j,Visible c (u j))
    (size : Fintype.card I≤2^(Fintype.card J)) {w : I→ℕ} (pos : ∀i,0<w i)
    (ge : 3≤∑i,w i) {θ : ℝ} (hit : θ∈attainable w c) :
    π-π/(Nat.clog 2 (∑i,w i):ℝ)≤θ := by
  apply R59.Mesh.dyadic_of_card ge
  intro lt
  have A:=(R54.Profile.fixed_profile pos (fun i=>exists_ne i) inj).mp hit
  apply R59.Mesh.kraft w (fun _=>Fintype.card J) (Fintype.card J) _ (fun _=>le_rfl)
  · simpa using size
  · exact common_reserve A lt u nz ind vis

theorem common_sendov {I J : Type*} [Fintype I] [Nontrivial I] [Fintype J]
    {c : I→Point} (inj : Function.Injective c) (u : J→Point) (nz : ∀j,u j≠0)
    (ind : ∀j k,j≠k→det (u j) (u k)≠0) (vis : ∀j,Visible c (u j))
    (size : Fintype.card I≤2^(Fintype.card J)) {w : I→ℕ} (pos : ∀i,0<w i)
    (ge : 3≤∑i,w i) {θ : ℝ} (hit : θ∈attainable w c) :
    Jsp404.alphaN (∑i,w i)≤θ :=
  (R59.Mesh.sendov_of_dyadic ge).trans (common_dyadic inj u nz ind vis size pos ge hit)
#print axioms common_reserve
#print axioms common_dyadic
#print axioms common_sendov
end R66.Common
