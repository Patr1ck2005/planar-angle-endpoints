import AllRows
import PlanarProfile

noncomputable section
open scoped Classical
namespace R58.Plane
open Real Finset JSP404 R37.SignedFan R58.FullRows

abbrev Fan := R37.SignedFan.Row
def gap (F : Fan) (j : Fin (F.n+1)) :=
  if j.val<F.n then F.u (j.val+1)-F.u j.val else F.u 0+π-F.u F.n

def cells (F : Fan) (l : ℝ) := ∑ j,⌊gap F j/l⌋₊
def digits (F : Fan) (l : ℝ) := ∑ j,(⌊gap F j/l⌋₊-1)

theorem long_gap (F : Fan) {l : ℝ} (ok : F.Legal l) : ∃ j,l≤gap F j := by
  by_contra! short
  have zero (j : ℕ) (hj : j<F.n) : F.step j=0 := by
    have h:=short (⟨j,by omega⟩ : Fin (F.n+1))
    simp only [gap,hj,ite_true] at h
    have lo:=F.step_budget ok j
    by_contra ne
    have one : F.step j=1 := by unfold Row.step at ne ⊢;split_ifs <;> simp_all
    rw [one] at lo
    norm_num at lo
    linarith
  have wrap:=short (Fin.last F.n)
  simp [gap] at wrap
  have bs:=F.seam_budget ok
  have seam : F.seam=0 := by
    by_contra ne
    have one : F.seam=1 := by unfold Row.seam at ne ⊢;split_ifs <;> simp_all
    rw [one] at bs
    norm_num at bs
    linarith
  have pc : F.prefixCount F.n=0 := Finset.sum_eq_zero (fun i hi=>zero i (Finset.mem_range.mp hi))
  have odd:=F.switches_odd
  simp [Row.switches,pc,seam] at odd

private def doubled (F : Fan) (i : ℕ) := if i<F.n+1 then F.u i else F.u (i-(F.n+1))+π

private theorem ordered_u (F : Fan) : Monotone F.u := by
  intro a b ab
  apply F.sorted.monotone
  exact min_le_min_right F.n ab

private def shifted (F : Fan) (s : Fin (F.n+1)) : R56.Windows.Row (F.n+1) where
  w i:=doubled F (s.val+i)
  ordered:=by
    intro i j ij jm
    unfold doubled
    split_ifs with hi hj hj
    · exact ordered_u F (by omega)
    · have a:=F.bounds (F.idx (s.val+i))
      have b:=F.bounds (F.idx (s.val+j-(F.n+1)))
      change F.u (s.val+i)≤F.u (s.val+j-(F.n+1))+π
      change 0≤F.u (s.val+j-(F.n+1)) ∧ _ at b
      change _ ∧ F.u (s.val+i)<π at a
      linarith
    · omega
    · exact add_le_add_left (ordered_u F (by omega)) _
  period:=by
    simp [doubled,show ¬s.val+(F.n+1)<F.n+1 by omega,s.isLt]

private theorem gap_shift (F : Fan) (s i : Fin (F.n+1)) :
    (shifted F s).w (i.val+1)-(shifted F s).w i=gap F (s+i) := by
  have si:=s.isLt
  have ii:=i.isLt
  change doubled F (s.val+(i.val+1))-doubled F (s.val+i.val)=_
  let q:=s.val+i.val
  change doubled F (q+1)-doubled F q=gap F (s+i)
  have total : q≤F.n+F.n := by dsimp [q];omega
  have val : (s+i).val=(if F.n+1≤q then q-(F.n+1) else q) := Fin.val_add_eq_ite s i
  by_cases early : q<F.n
  · simp [gap,doubled,val,early,show ¬F.n+1≤q by omega,show q+1<F.n+1 by omega,
      show q<F.n+1 by omega]
  by_cases atEnd : q=F.n
  · rw [atEnd] at val ⊢
    simp [doubled,gap,val]
  have past : F.n+1≤q := by omega
  have small : q-(F.n+1)<F.n := by omega
  have delta : q+1-(F.n+1)=(q-(F.n+1))+1 := by omega
  simp [doubled,gap,val,past,small,show ¬q<F.n+1 by omega,show ¬q+1<F.n+1 by omega,delta]


private theorem sum_perm (F : Fan) (s : Fin (F.n+1)) (f : Fin (F.n+1)→ℕ) :
    (∑ i,f (s+i))=∑ i,f i := Equiv.sum_comp (Equiv.addLeft s) f

private theorem as_circ {p : Point} {t : ℝ} {b : Bool} {r : ℝ} (pos : 0<r)
    (eq : p=r • oriented t b) : ∃ z : ℝ,z≠0 ∧ p=z • circleDirection t := by
  cases b
  · exact ⟨-r,neg_ne_zero.mpr pos.ne',by simpa [oriented] using eq⟩
  · exact ⟨r,pos.ne',by simpa [oriented] using eq⟩

private theorem circ_pi (t : ℝ) : circleDirection (t+π)= -circleDirection t := by
  ext i
  fin_cases i <;> simp [circleDirection]

private theorem represented {F : Fan} (s j : Fin (F.n+1)) {x : Point} {r : ℝ} (nz : r≠0)
    (eq : x=r • circleDirection (F.bearing j)) :
    ∃ i : Fin (F.n+1),∃ z : ℝ,z≠0 ∧ x=z • circleDirection ((shifted F s).w i) := by
  obtain ⟨i,e⟩:=(Equiv.addLeft s).surjective j
  change s+i=j at e
  have val:=congrArg Fin.val e
  rw [Fin.val_add_eq_ite] at val
  have hu : F.u j.val=F.bearing j := by
    apply congrArg F.bearing
    exact Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ j.isLt))
  by_cases right : F.n+1≤s.val+i.val
  · simp only [right,ite_true] at val
    refine ⟨i,-r,neg_ne_zero.mpr nz,?_⟩
    change x= -r • circleDirection (doubled F (s.val+i.val))
    rw [doubled,ite_eq_right (by omega : ¬ s.val+i.val<F.n+1),val,hu,circ_pi]
    simpa using eq
  · simp only [right,ite_false] at val
    refine ⟨i,r,nz,?_⟩
    change x=r • circleDirection (doubled F (s.val+i.val))
    rw [doubled,ite_eq_left (by omega : s.val+i.val<F.n+1),val,hu]
    exact eq

/-- Genuine signed rows supply the cut, the full set of walls and a cyclic
permutation of the original gap lengths. -/
theorem row_chart {I : Type*} (F : Fan) (x : I→Point) {l : ℝ} (lp : 0<l)
    (obs : F.Represents x) (legal : F.Legal l) :
    ∃ R : R56.Windows.Row (F.n+1),
      0<cell R l F.n ∧ cellSum R l (F.n+1)=cells F l ∧
      (∑ i : Fin (F.n+1),R.digits i l)=digits F l ∧
      ∀ q,∃ j : Fin (F.n+1),∃ r : ℝ,r≠0 ∧ x q=r • circleDirection (R.w j) := by
  obtain ⟨p,big⟩:=long_gap F legal
  let s : Fin (F.n+1):=p-Fin.last F.n
  have last : s+Fin.last F.n=p := sub_add_cancel _ _
  have he (j : Fin (F.n+1)) : cell (shifted F s) l j=⌊gap F (s+j)/l⌋₊ := by
    unfold cell
    rw [gap_shift F s j]
  refine ⟨shifted F s,?_,?_,?_,?_⟩
  · have eq:=he (Fin.last F.n)
    rw [last] at eq
    change 0<cell (shifted F s) l (Fin.last F.n).val
    rw [eq]
    exact Nat.le_floor ((le_div_iff₀ lp).mpr (by simpa using big))
  · change (∑ i∈Finset.range (F.n+1),cell (shifted F s) l i)=_
    rw [←Fin.sum_univ_eq_sum_range]
    simp_rw [he]
    exact sum_perm F s (fun j=>⌊gap F j/l⌋₊)
  · change (∑ j : Fin (F.n+1),(cell (shifted F s) l j-1))=_
    simp_rw [he]
    exact sum_perm F s (fun j=>⌊gap F j/l⌋₊-1)
  · intro q
    obtain ⟨j,r,hr,h⟩:=obs.1 q
    obtain ⟨r,rn,e⟩:=as_circ hr h
    exact represented s j rn e

end R58.Plane
#print axioms R58.Plane.row_chart
