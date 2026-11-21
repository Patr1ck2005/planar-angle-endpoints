import InteriorSemicircle

noncomputable section
namespace R91.Interior
open JSP404 Real Finset InnerProductGeometry R87.Diameter R55.WeightedCollision

/-- Fix any external center j in advance. The extremal signed headings
relative to its chord complete a surrounding triple whose three angles sum to 2π. -/
theorem anchored_three {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {i j : I} (ji : j≠i) (inside : c i∈convexHull ℝ (c '' {a | a≠i}))
    {δ : ℝ} (dp : 0<δ) (mac : Macro c (π-δ)) :
    ∃k l,k≠i ∧ l≠i ∧ j≠k ∧ j≠l ∧ k≠l ∧
      (EuclideanGeometry.angle (c j) (c i) (c k)+EuclideanGeometry.angle (c k) (c i) (c l)+
        EuclideanGeometry.angle (c l) (c i) (c j)=2*π) ∧
      2*δ≤EuclideanGeometry.angle (c j) (c i) (c k) ∧
      2*δ≤EuclideanGeometry.angle (c k) (c i) (c l) ∧
      2*δ≤EuclideanGeometry.angle (c l) (c i) (c j) := by
  classical
  let O:={a : I // a≠i}
  let ref : O:=⟨j,ji⟩
  let : Nonempty O:=⟨ref⟩
  obtain ⟨t,T⟩:=head_exists (sub_ne_zero.mpr (ci.ne ji))
  have choose_head (k : O) : ∃a:ℝ,-π≤a ∧ a≤π ∧ Head (c k.val-c i) (t+a) ∧ (k=ref→a=0) := by
    by_cases eq:k=ref
    · subst k
      exact ⟨0,by linarith [pi_pos],pi_pos.le,by simpa [ref] using T,fun _=>rfl⟩
    · obtain ⟨a,lo,hi,A⟩:=full_head _ (sub_ne_zero.mpr (ci.ne k.property)) t
      exact ⟨a,lo,hi,A,fun h=>False.elim (eq h)⟩
  choose s lo hi H zero using choose_head
  have fromRef (a : O) : EuclideanGeometry.angle (c j) (c i) (c a.val)=|s a| := by
    change angle (c j-c i) (c a.val-c i)=_
    have neg : t-(t+s a)= -(s a):=by ring
    simpa only [neg,abs_neg] using head_angle T (H a) (by rw [neg,abs_neg];exact abs_le.mpr ⟨lo a,hi a⟩)
  have strict (a : O) : |s a|<π := by
    by_cases eq:a=ref
    · subst a;rw [zero ref rfl,abs_zero];exact pi_pos
    · have ja : j≠a.val:=by intro h;apply eq;exact Subtype.ext h.symm
      have cap:=mac j i a.val ji ja a.property.symm
      rw [fromRef] at cap;linarith
  obtain ⟨k,_,lk⟩:=exists_min_image (univ : Finset O) s univ_nonempty
  obtain ⟨l,_,hl⟩:=exists_max_image (univ : Finset O) s univ_nonempty
  have span : π≤s l-s k:=semicircle_span i inside (t:=t) (fun a ai=>
    ⟨s ⟨a,ai⟩,lk _ (mem_univ _),hl _ (mem_univ _),H ⟨a,ai⟩⟩)
  have sk : s k<0:=by linarith [(abs_lt.mp (strict l)).2]
  have sl : 0<s l:=by linarith [(abs_lt.mp (strict k)).1]
  have jk : j≠k.val:=by
    intro h
    have eq:k=ref:=Subtype.ext h.symm
    linarith [zero k eq]
  have jl : j≠l.val:=by
    intro h
    have eq:l=ref:=Subtype.ext h.symm
    linarith [zero l eq]
  have kl : k.val≠l.val:=by
    intro h
    have eq:k=l:=Subtype.ext h
    rw [eq] at sk;linarith
  have X:=fromRef k
  rw [abs_of_neg sk] at X
  have Y:=fromRef l
  rw [abs_of_pos sl,EuclideanGeometry.angle_comm] at Y
  have Z:=wrap_angle (H k) (H l) span (by linarith [lo k,hi l])
  change EuclideanGeometry.angle (c k.val) (c i) (c l.val)=_ at Z
  have tot : EuclideanGeometry.angle (c j) (c i) (c k.val)+EuclideanGeometry.angle (c k.val) (c i) (c l.val)+
        EuclideanGeometry.angle (c l.val) (c i) (c j)=2*π := by linarith only [X,Y,Z]
  have left:=mac j i k.val ji jk k.property.symm
  have mid:=mac k.val i l.val k.property kl l.property.symm
  have right:=mac l.val i j l.property jl.symm ji.symm
  exact ⟨k.val,l.val,k.property,l.property,jk,jl,kl,tot,by linarith,by linarith,by linarith⟩

/-- An existential three-chord kit on any actual interior label. -/
theorem three_chords {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {i : I} (inside : c i∈convexHull ℝ (c '' {a | a≠i}))
    {δ : ℝ} (dp : 0<δ) (mac : Macro c (π-δ)) :
    ∃h : Fin 3↪I,(∀a,h a≠i) ∧ ∀a b,a≠b →
      2*δ≤EuclideanGeometry.angle (c (h a)) (c i) (c (h b)) ∧
      EuclideanGeometry.angle (c (h a)) (c i) (c (h b))≤π-δ := by
  classical
  have ex:=convexHull_nonempty_iff.mp (show (convexHull ℝ (c '' {a | a≠i})).Nonempty from ⟨_,inside⟩)
  obtain ⟨_,j,ji,rfl⟩:=ex
  obtain ⟨k,l,ki,li,jk,jl,kl,_,A,B,C⟩:=anchored_three ci ji inside dp mac
  let h : Fin 3↪I := ⟨![j,k,l],by
    intro a b eq
    fin_cases a <;> fin_cases b <;> simp_all⟩
  have ext (a : Fin 3) : h a≠i:=by fin_cases a <;> first | exact ji | exact ki | exact li
  refine ⟨h,ext,?_⟩
  intro a b ab
  refine ⟨?_,mac _ _ _ (ext a) (h.injective.ne ab) (ext b).symm⟩
  have A' : 2*δ≤EuclideanGeometry.angle (c k) (c i) (c j):=by rwa [EuclideanGeometry.angle_comm]
  have B' : 2*δ≤EuclideanGeometry.angle (c l) (c i) (c k):=by rwa [EuclideanGeometry.angle_comm]
  have C' : 2*δ≤EuclideanGeometry.angle (c j) (c i) (c l):=by rwa [EuclideanGeometry.angle_comm]
  fin_cases a <;> fin_cases b <;> first | exact (ab rfl).elim | exact A | exact B | exact C | exact A' | exact B' | exact C'

end R91.Interior
#print axioms R91.Interior.anchored_three
#print axioms R91.Interior.three_chords
