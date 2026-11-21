import WindowAxes
import AxisChart
noncomputable section
namespace R54.GapTest
open Real JSP404 InnerProductGeometry R56.Windows

private theorem cover {m:ℕ} (w:ℕ→ℝ) {x:ℝ} (mp:0<m) (lo:w 0≤x) (hi:x≤w m) :
    ∃i:Fin m,w i≤x ∧ x≤w (i.val+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases left:w m≤x
    · exact ⟨Fin.last m,left,hi⟩
    · have pos:0<m:=by
        by_contra! z
        have e:m=0:=by omega
        exact left (e.symm ▸ lo)
      obtain ⟨i,a,b⟩:=ih pos (le_of_not_ge left)
      exact ⟨i.castSucc,a,b⟩

/-- The converse to site insertion also holds for arbitrary repeated walls. -/
theorem packing {m d:ℕ} (R:Row m) {δ:ℝ} (positive:0<δ) (a:Fin d→ℝ)
    (bounds:∀p,R.w 0≤a p ∧ a p≤R.w m)
    (sep:∀p q,p≠q→δ≤|a p-a q|)
    (wall:∀p j,j≤m→δ≤|a p-R.w j|) :
    d≤R51.Anchored.gapScore m R.w δ := by
  classical
  have mp:0<m:=by
    by_contra! h
    have z:m=0:=by omega
    have per:=R.period
    have eq:R.w m=R.w 0:=congrArg R.w z
    linarith [pi_pos]
  have inj:Function.Injective a:=by
    intro p q eq
    by_contra ne
    have b:=sep _ _ ne
    rw [eq,sub_self,abs_zero] at b
    linarith
  let A:=Finset.univ.image a
  have count:A.card=d:=by simp [A,Finset.card_image_of_injective _ inj]
  let box (i:Fin m):=A.filter (fun x=>R.w i≤x ∧ x≤R.w (i.val+1))
  have all:A⊆Finset.univ.biUnion box:=by
    intro x mem
    obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp mem
    obtain ⟨i,low,high⟩:=cover R.w mp (bounds p).1 (bounds p).2
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨mem,low,high⟩⟩
  have each (i:Fin m) : (box i).card≤R.digits i δ:=by
    rcases (box i).eq_empty_or_nonempty with e|ne
    · simp [e]
    have span:=R51.Anchored.interval_span (box i) positive ne (R.w i+δ) (R.w (i.val+1)-δ) (by
      intro x hx
      obtain ⟨h,low,high⟩:=Finset.mem_filter.mp hx
      obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp h
      have l:=wall p i.val i.isLt.le
      have r:=wall p (i.val+1) i.isLt
      rw [abs_of_nonneg (sub_nonneg.mpr low)] at l
      rw [abs_of_nonpos (sub_nonpos.mpr high)] at r
      exact ⟨by linarith,by linarith⟩) (by
      intro x hx y hy neq
      obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hx).1
      obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hy).1
      exact sep p q (fun e=>neq (congrArg a e)))
    have space:(((box i).card+1:ℕ):ℝ)≤(R.w (i.val+1)-R.w i)/δ:=by
      apply (le_div_iff₀ positive).mpr
      push_cast
      linarith
    have whole:=(Nat.le_floor space)
    unfold Row.digits
    omega
  calc d=A.card:=count.symm
       _≤(Finset.univ.biUnion box).card:=Finset.card_le_card all
       _≤∑i,(box i).card:=Finset.card_biUnion_le
       _≤∑i,R.digits i δ:=Finset.sum_le_sum (fun i _=>each i)

/-- Every wall of the lifted row, including the repeated closing wall, has
an actual external macrocenter as a witness. -/
def Witnessed {I:Type*} {m:I→ℕ} (R:∀i,Row (m i)) (c:I→Point) : Prop :=
  ∀i j,j≤m i→∃k,i≠k ∧ Bearing (c k-c i) ((R i).w j)

theorem axes_bound {I:Type*} [Fintype I] {m d:I→ℕ} (R:∀i,Row (m i)) {c:I→Point} {δ:ℝ}
    (positive:0<δ) (witness:Witnessed R c) (A:R56.Decorated.Axes c d (π-δ)) :
    ∀i,d i≤score R i δ := by
  intro i
  let t:=(R i).w 0
  choose a below above line using fun p=>lifted_polar (A.v i p) (A.nonzero i p) t
  have span {u v:ℝ} (u0:t≤u) (ut:u≤t+π) (v0:t≤v) (vt:v≤t+π) : |u-v|≤π :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  apply packing (R i) positive a (fun p=>⟨below p,by rw [(R i).period];exact above p⟩)
  · intro p q neq
    apply apart (line p) (line q) (span (below p) (above p) (below q) (above q))
    intro r hr
    simpa only [one_smul] using A.internal i p q neq r 1 hr (Or.inr rfl)
  · intro p j jle
    obtain ⟨k,ne,chord⟩:=witness i j jle
    have lo:t≤(R i).w j:=(R i).ordered (Nat.zero_le j) jle
    have hi:(R i).w j≤t+π:=((R i).ordered jle le_rfl).trans_eq (R i).period
    exact apart (line p) chord (span (below p) (above p) lo hi) (A.outside i k ne p)

#print axioms packing
#print axioms axes_bound
end R54.GapTest
