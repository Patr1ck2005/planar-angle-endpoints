import ClusterContraction

noncomputable section
open scoped Classical
namespace R62.Contraction
open Real JSP404 R51.Anchored R54.Profile R54.GapTest R55.WeightedCollision R56.Windows

variable {I J : Type*} [Fintype I] [Fintype J] {m : I → ℕ} {c : I → Point} {δ : ℝ}

/-- The complete dyadic row capacities of the actual configuration, simultaneously. -/
theorem full_cluster (R : ∀ i, Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (ci : Function.Injective c) (dp : 0<δ) (θpos : 0≤π-δ) (legal : Macro c (π-δ))
    (U : Finset I) {k : ℕ} (kp : 0<k) {t : ℝ} (ht : 0≤t ∧ t<π) (W η : ℕ→ℝ)
    (B : Fin k→ℕ) (first : W 0=t) (last : W k=t+π)
    (wall : ∀ j≤k, Wall (Finset.univ.image c) (U.image c) t (W j) (η j))
    (fit : ∀ j : Fin k, W (j.val+1)-W j+η j+η (j.val+1)<((B j:ℝ)+2)*δ) :
    ∑ i ∈ U,2^score R i δ ≤ 2^(∑ j,B j) := by
  let w := fun i => 2^score R i δ
  have pos (i : I) : 0<w i := pow_pos (by decide) _
  have D (i : I) : dim w i ≤ score R i δ :=
    (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr (le_refl _)
  have att := gap_realization R dp front back pos ci θpos legal D
  apply weighted_cluster ci pos att U kp t ht W η B first last wall (by linarith)
  simpa using fit

/-- Each end error is charged once in its gap, with exact floor semantics. -/
theorem full_cluster_floor (R : ∀ i, Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (ci : Function.Injective c) (dp : 0<δ) (θpos : 0≤π-δ) (legal : Macro c (π-δ))
    (U : Finset I) {k : ℕ} (kp : 0<k) {t : ℝ} (ht : 0≤t ∧ t<π) (W η : ℕ→ℝ)
    (first : W 0=t) (last : W k=t+π)
    (wall : ∀ j≤k, Wall (Finset.univ.image c) (U.image c) t (W j) (η j)) :
    ∑ i ∈ U,2^score R i δ ≤ 2^(∑ j : Fin k,
      (⌊(W (j.val+1)-W j+η j+η (j.val+1))/δ⌋₊-1)) := by
  apply full_cluster R front back ci dp θpos legal U kp ht W η _ first last wall
  intro j
  let d:=W (j.val+1)-W j+η j+η (j.val+1)
  let b:=⌊d/δ⌋₊
  have h := (div_lt_iff₀ dp).mp (Nat.lt_floor_add_one (d/δ))
  have ar : b+1≤(b-1)+2 := by omega
  have cast : (b:ℝ)+1≤((b-1:ℕ):ℝ)+2 := by exact_mod_cast ar
  exact h.trans_le (mul_le_mul_of_nonneg_right cast dp.le)

omit [Fintype I] in
/-- Retaining a subset of centers can only create room in each of its rows. -/
theorem retained_row (R : ∀ i, Row (m i)) (front : Represents R c)
    (e : J ↪ I) {q : J→ℕ} (Q : ∀ j,Row (q j)) (back : Witnessed Q (c ∘ e))
    (dp : 0<δ) (j : J) : score R (e j) δ ≤ score Q j δ := by
  let A:=full_axes R dp front
  let rest : R56.Decorated.Axes (c ∘ e) (fun j=>score R (e j) δ) (π-δ) :=
    ⟨fun j=>A.v (e j),fun j=>A.nonzero (e j),fun j=>A.internal (e j),
     fun i j ne=>A.outside (e i) (e j) (e.injective.ne ne)⟩
  exact axes_bound Q dp back rest j

/-- Keep the indicated representative a and every center outside its fiber. -/
def mergedFiber (e : J ↪ I) (a : J) : Finset I := Finset.univ \ ((Finset.univ.erase a).map e)

/-- At unchanged angular defect, merging the fiber leaves at least the old total potential.
The window test is at the retained representative; all other retained rows grow by monotonicity. -/
theorem no_jump (R : ∀ i, Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (ci : Function.Injective c) (dp : 0<δ) (θpos : 0≤π-δ) (legal : Macro c (π-δ))
    (e : J ↪ I) {q : J→ℕ} (Q : ∀ j, Row (q j)) (kept : Witnessed Q (c ∘ e))
    (a : J) (ht : 0≤(Q a).w 0 ∧ (Q a).w 0<π) (η : ℕ→ℝ)
    (wall : ∀ j≤q a, Wall (Finset.univ.image c) ((mergedFiber e a).image c)
      ((Q a).w 0) ((Q a).w j) (η j))
    (fit : ∀ j : Fin (q a), (Q a).w (j.val+1)-(Q a).w j+η j+η (j.val+1)<
      (((Q a).digits j δ:ℝ)+2)*δ) :
    ∑ i,2^score R i δ ≤ ∑ j,2^score Q j δ := by
  classical
  have qp : 0<q a := by
    by_contra! bad
    have h:= (Q a).period
    have he := congrArg (Q a).w (show q a=0 by omega)
    linarith [pi_pos]
  let S := (Finset.univ.erase a).map e
  let v := fun i => 2^score R i δ
  let u := fun j => 2^score Q j δ
  have fiber : ∑ i ∈ mergedFiber e a, v i ≤ u a :=
    full_cluster R front back ci dp θpos legal _ qp ht _ η _ rfl (Q a).period wall fit
  have keptSum : ∑ i ∈ S,v i ≤ ∑ j ∈ Finset.univ.erase a,u j := by
    rw [Finset.sum_map]
    exact Finset.sum_le_sum (fun j _=>Nat.pow_le_pow_right (by decide : 0<2)
      (retained_row R front e Q kept dp j))
  calc ∑ i,v i = (∑ i ∈ mergedFiber e a,v i) + ∑ i ∈ S,v i :=
         (Finset.sum_sdiff (Finset.subset_univ S)).symm
       _ ≤ u a + ∑ j ∈ Finset.univ.erase a,u j := Nat.add_le_add fiber keptSum
       _ = ∑ j,u j := by rw [add_comm,Finset.sum_erase_add _ _ (Finset.mem_univ a)]
end R62.Contraction
#print axioms R62.Contraction.full_cluster_floor
#print axioms R62.Contraction.no_jump

