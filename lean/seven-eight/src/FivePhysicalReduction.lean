import PhysicalBoardData
import FourMarkedEndpoint
import MarkedThinning
noncomputable section
namespace R67.Board
open Real JSP404 R55.WeightedCollision R66.Five Finset R67.Circle

/-- The finite (thinned) five-center angular statement, expressed directly
in the real global gaps and incidence groups. -/
def FiniteBoardLaw : Prop :=
  ∀(o : Equiv.Perm (Fin 10)),OrientOK o→∀(f : Fin 10→ℝ),(∀a,0≤f a ∧ f a≤2)→MacroOK o f→
  ∀(k : ℕ),k≤20→∀(u : Fin 5) (p : Option (Fin 5)),p≠some u→
  (∀i,i≠u→k+(if p=some i then 1 else 0)≤exponent (group o) f i)→
  (k:ℝ)+(if p.isSome then 3 else 5/2)≤R67.Board.total f

private theorem transport {I : Type*} [Fintype I] {c : I→Point} {w : I→ℕ} {θ : ℝ}
    (e : Equiv.Perm I) (A : Admissible w c θ) : Admissible (w ∘ e) (c ∘ e) θ := by
  obtain ⟨pos,mac,v,unit,inter,out⟩:=A
  exact ⟨pos,fun i j k ij ik jk=>mac _ _ _ (e.injective.ne ij) (e.injective.ne ik) (e.injective.ne jk),
    fun i=>v (e i),fun i=>unit (e i),fun i=>inter (e i),fun i j ne=>out _ _ (e.injective.ne ne)⟩

private def required (o : Equiv.Perm (Fin 10)) (s : Finset (Fin 10)) : Prop :=
  ∃ i j k : Fin 5,i<j ∧ j<k ∧
    let p:=idx o i j; let q:=idx o i k;let r:=idx o j k
    let a:=if p<r then p else r
    let c:=if p<r then r else p
    s=univ \ arc a q ∨ s=univ \ arc q c ∨ s=univ \ arc c a

private theorem laws (o : Equiv.Perm (Fin 10)) (g : Fin 10→ℝ) :
    MacroOK o g ↔ legal (required o) g := by
  constructor
  · intro L s req
    obtain ⟨i,j,k,ij,jk,mem⟩:=req
    have h:=L i j k ij jk
    by_cases m:idx o i j < idx o j k
    · simp only [ite_eq_left m] at h mem
      rcases mem with rfl|rfl|rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    · simp only [ite_eq_right m] at h mem
      rcases mem with rfl|rfl|rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  · intro legal i j k ij jk
    by_cases m:idx o i j < idx o j k
    · simp only [ite_eq_left m]
      refine ⟨legal _ ⟨i,j,k,ij,jk,?_⟩,legal _ ⟨i,j,k,ij,jk,?_⟩,legal _ ⟨i,j,k,ij,jk,?_⟩⟩ <;> simp [m]
    · simp only [ite_eq_right m]
      refine ⟨legal _ ⟨i,j,k,ij,jk,?_⟩,legal _ ⟨i,j,k,ij,jk,?_⟩,legal _ ⟨i,j,k,ij,jk,?_⟩⟩ <;> simp [m]

theorem excludes_marked (law : FiniteBoardLaw) {c : Fin 5→Point} (inj : Function.Injective c)
    {w : Fin 5→ℕ} {θ : ℝ} (hit : Admissible w c θ) (lt : θ<π)
    (u : Fin 5) (p : Option (Fin 5)) (different : p≠some u) (k : ℕ)
    (enough : ∀i,i≠u→k+(if p=some i then 1 else 0)≤Nat.clog 2 (w i)) :
    (k:ℝ)+(if p.isSome then 3 else 5/2)≤π/(π-θ) := by
  obtain ⟨e,⟨C⟩⟩:=sorted_chart c inj
  let W:=w ∘ e
  have A:=transport e hit
  obtain ⟨o,asc⟩:=sort_scalar (bearing C)
  let x (s : Slot):=bearing C (o s)/(π-θ)
  let T:=π/(π-θ)
  let g:=gaps x T
  have pos:=sub_pos.mpr lt
  have mono : Monotone x := fun i j h=>div_le_div_of_nonneg_right (asc h) pos.le
  have bounded (i : Slot) : 0≤x i ∧ x i<T :=
    ⟨div_nonneg (bearing_bounds C _).1 pos.le,div_lt_div_of_pos_right (bearing_bounds C _).2 pos⟩
  have nn:∀i,0≤g i:=gap_nonneg x T mono bounded
  obtain ⟨ori,mac⟩:=macro_data C (inj.comp e.injective) lt A.2.1 o asc
  let P:=p.map e.symm
  have same (i : Fin 5) : P=some i ↔ p=some (e i) := by cases p <;> simp [P,Equiv.symm_apply_eq]
  have diff : P≠some (e.symm u) := fun h=>different (by simpa using (same _).mp h)
  have rows (i : Fin 5) (ne : i≠e.symm u) : k+(if P=some i then 1 else 0)≤exponent (group o) g i := by
    have neq : e i≠u := fun h=>ne (e.eq_symm_apply.mpr h)
    have h:=physical_row_budget C o asc A lt i
    rw [slot_cost_eq] at h
    rw [if_congr (same i) rfl rfl]
    apply (enough _ neq).trans
    convert h using 1 <;> try rfl
    unfold exponent digit width fiber R67.Circle.length
    apply sum_congr rfl;intro j _
    congr! 8 <;> first | rfl | exact Subsingleton.elim _ _ | (ext a;simp)
  by_contra! strict
  have tot : R67.Board.total g=T := R67.Circle.total x T
  have band : R67.Board.total g<(k:ℝ)+(if P.isSome then 3 else 5/2) := by
    rw [tot]; simpa [T,P] using strict
  obtain ⟨s,_,cap,f,box,small,legal,_,fit⟩:=thin_farkas (group o) (required o) (e.symm u) P k g nn band ((laws _ _).mp mac) rows
  exact small.not_ge (law o ori f box ((laws _ _).mpr legal) s cap _ P diff fit)

theorem five_of_finite (law : FiniteBoardLaw) {c : Fin 5→Point} (ci : Function.Injective c)
    (v : Fin 5→ℕ) (vp : ∀i,0<v i) {θ : ℝ} (hit : θ∈attainable v c) : Jsp404.alphaN (∑i,v i)≤θ := by
  apply ((all_weights_iff_marked ci).mpr ?_) v vp θ hit
  constructor
  · intro k u t A
    by_contra! bad
    have denom : 0<2*(k:ℝ)+5:=by positivity
    have lt : t<π:=by linarith [div_pos (by positivity : 0<2*π) denom]
    have b:=excludes_marked law ci A lt u none (by simp) k (by
      intro i ne;simp [lowMarks,ne,Nat.clog_pow 2 k (by decide)])
    have pos:=sub_pos.mpr lt
    simp only [Option.isSome_none,Bool.false_eq_true,ite_false,le_div_iff₀ pos] at b
    have hh:=(div_lt_iff₀ denom).mp (show 2*π/(2*(k:ℝ)+5)<π-t by linarith)
    nlinarith only [hh,b]
  · intro k u p t A
    by_contra! bad
    have denom : 0<(k:ℝ)+3:=by positivity
    have lt : t<π:=by linarith [div_pos pi_pos denom]
    have d:u.succAbove p≠u:=Fin.succAbove_ne _ _
    have b:=excludes_marked law ci A lt u (some (u.succAbove p)) (by simpa using d) k (by
      intro i ne;by_cases h:i=u.succAbove p
      · subst i;simp [highMarks,Nat.clog_pow 2 (k+1) (by decide)]
      · simp [highMarks,h,lowMarks,ne,Ne.symm h,Nat.clog_pow 2 k (by decide)])
    have pos:=sub_pos.mpr lt
    simp only [Option.isSome_some,ite_true,le_div_iff₀ pos] at b
    have hh:=(div_lt_iff₀ denom).mp (show π/((k:ℝ)+3)<π-t by linarith)
    nlinarith only [hh,b]
#print axioms excludes_marked
#print axioms five_of_finite
end R67.Board
