import FullRows

noncomputable section
open scoped Classical
namespace R58.AllRows
open Finset Real JSP404 R56.Windows R58.FullRows

variable {m : ℕ} (R : Row m) (l : ℝ)

def used (j : ℕ) := ∑ i∈Finset.range j,if 0<cell R l i then 1 else 0

theorem used_mono : Monotone (used R l) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [used,Finset.sum_range_succ]
  omega

theorem used_end : used R l m=(long R l).card := by
  rw [show used R l m=∑ j : Fin m, if 0<cell R l j then 1 else 0 from
    (Fin.sum_univ_eq_sum_range (fun j=>if 0<cell R l j then 1 else 0) m).symm]
  simp [long]

private theorem same_prefix {i j : ℕ} (ij : i≤j) (same : used R l i=used R l j) :
    cellSum R l i=cellSum R l j := by
  induction j with
  | zero =>
    have eq : i=0 := by omega
    rw [eq]
  | succ j ih =>
    by_cases eq : i=j+1
    · rw [eq]
    have be:=used_mono R l (show i≤j by omega)
    have step : used R l (j+1)=used R l j+(if 0<cell R l j then 1 else 0) := by
      simp only [used,Finset.sum_range_succ]
    by_cases pos : 0<cell R l j
    · simp [pos] at step
      omega
    · have z : cell R l j=0 := by omega
      have e : used R l i=used R l j := by simpa [step,pos] using same
      simpa [cellSum,Finset.sum_range_succ,z] using ih (by omega) e

/-- Use one fresh label at every long gap and at every half-defect of cumulative
unused width. Equal labels have ordinary projective bearing span < l/2. -/
theorem palette (lp : 0<l) (last : 0<cell R l (m-1)) {N : ℕ}
    (budget : 2*π<((N:ℝ)+1)*l) :
    ∃ tag : Fin m→ℕ,
      (∀ i,tag i+(∑ j : Fin m,R.digits j l)+cellSum R l m<N) ∧
      ∀ i j,tag i=tag j → |R.w i-R.w j|<l/2 := by
  let z (i : ℕ) := (remainder R l i-R.w 0)/(l/2)
  let tag (i : Fin m) := used R l i+⌊z i⌋₊
  have hp : 0<l/2 := by linarith
  have ord {i j : ℕ} (ij : i≤j) (jm : j≤m) : z i≤z j :=
    div_le_div_of_nonneg_right (sub_le_sub_right (remainder_order R l lp ij jm) _) hp.le
  have z0 : z 0=0 := by simp [z,remainder,cellSum]
  have nn {i : ℕ} (im : i≤m) : 0≤z i := z0 ▸ ord (Nat.zero_le _) im
  have before (i : Fin m) : used R l i<used R l m := by
    have mi:=i.isLt
    have eq : m=(m-1)+1 := by omega
    have step : used R l m=used R l (m-1)+1 := by
      calc
        used R l m=used R l ((m-1)+1) := congrArg (used R l) eq
        _=used R l (m-1)+1 := by simp only [used,Finset.sum_range_succ,ite_eq_left last]
    have h:=used_mono R l (show i.val≤m-1 by omega)
    omega
  have outside : (⌊z m⌋₊+2*cellSum R l m)≤N := by
    have h:=(le_div_iff₀ hp).mp (Nat.floor_le (nn (i:=m) le_rfl))
    change (⌊z m⌋₊:ℝ)*(l/2)≤R.w m-(cellSum R l m:ℝ)*l-R.w 0 at h
    rw [R.period] at h
    by_contra! bad
    have bc : (N:ℝ)+1≤(⌊z m⌋₊:ℝ)+2*(cellSum R l m:ℝ) := by exact_mod_cast bad
    nlinarith [mul_le_mul_of_nonneg_right bc lp.le]
  refine ⟨tag,?_,?_⟩
  · intro i
    have h:=before i
    rw [used_end] at h
    have u:=Nat.floor_le_floor (ord i.isLt.le le_rfl)
    have eq:=digits_plus_long R l
    change used R l i+⌊z i⌋₊+_+_<N
    omega
  · have forward (i j : Fin m) (ij : i.val≤j.val) (eq : tag i=tag j) : |R.w i-R.w j|<l/2 := by
      have ue:=used_mono R l ij
      have fe:=Nat.floor_le_floor (ord ij j.isLt.le)
      change used R l i+⌊z i⌋₊=used R l j+⌊z j⌋₊ at eq
      have us : used R l i=used R l j := by omega
      have fs : ⌊z i⌋₊=⌊z j⌋₊ := by omega
      have pr:=same_prefix R l ij us
      have lo:=Nat.floor_le (nn i.isLt.le)
      have hi:=Nat.lt_floor_add_one (z j)
      rw [←fs] at hi
      have clos : z j-z i<1 := by linarith
      have h : remainder R l j-R.w 0-(remainder R l i-R.w 0)<l/2 := by
        apply (div_lt_one hp).mp
        simpa only [sub_div,z] using clos
      unfold remainder at h
      rw [pr] at h
      rw [abs_of_nonpos (sub_nonpos.mpr (R.ordered ij j.isLt.le))]
      linarith
    intro i j eq
    rcases le_total i.val j.val with h|h
    · exact forward i j h eq
    · rw [abs_sub_comm];exact forward j i h eq.symm

/-- No row saturation hypothesis. Every finite ordinary plane configuration obeys
the joint inequality on the digit exponents and total occupied integer cells. -/
theorem capacity (S : Finset Point) (m : Point→ℕ) (R : ∀ v,Row (m v))
    {l : ℝ} (lp : 0<l) (upper : l≤π) (legal : maxAngle S≤π-l)
    (last : ∀ v∈S,0<cell (R v) l (m v-1))
    (rep : ∀ v∈S,∀ u∈S,v≠u → ∃ j : Fin (m v),∃ r : ℝ,r≠0 ∧ u-v=r • circleDirection ((R v).w j)) :
    (∑ v∈S,2^((∑ j : Fin (m v),(R v).digits j l)+cellSum (R v) l (m v)))≤2^⌊2*π/l⌋₊ := by
  classical
  let N:=⌊2*π/l⌋₊
  have budget : 2*π<((N:ℝ)+1)*l := (div_lt_iff₀ lp).mp (Nat.lt_floor_add_one _)
  have row (v : Point) (hv : v∈S) := palette (R v) l lp (last v hv) budget
  choose tag lim close using row
  let present (v u : Point) := v∈S ∧ u∈S ∧ v≠u
  let wall (v u : Point) (h : present v u) := (rep v h.1 u h.2.1 h.2.2).choose
  let c (v u : Point) := if h : present v u then tag v h.1 (wall v u h) else 0
  let k (v : Point) := (∑ j : Fin (m v),(R v).digits j l)+cellSum (R v) l (m v)
  apply R58.Knockout.planar_capacity S c N k lp legal
  · intro v hv a ha b hb va vb ab eq
    have pa : present v a:=⟨hv,ha,va⟩
    have pb : present v b:=⟨hv,hb,vb⟩
    simp only [c,dite_eq_left pa,dite_eq_left pb] at eq
    have small:=close v hv _ _ eq
    obtain ⟨r,rn,ea⟩:=(rep v hv a ha va).choose_spec
    obtain ⟨s,sn,eb⟩:=(rep v hv b hb vb).choose_spec
    have law:=(angle_le_maxAngle ha hv hb va.symm ab vb).trans legal
    change InnerProductGeometry.angle (a-v) (b-v)≤_ at law
    change InnerProductGeometry.angle (a-v) (b-v)<_
    rw [ea,eb] at law ⊢
    exact true_angle rn sn lp upper small law
  · intro v hv
    by_cases any : (S.erase v).Nonempty
    · have sub : R58.Knockout.colors S c v⊆Finset.range (N-k v) := by
        intro x hx
        obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
        obtain ⟨ne,us⟩:=Finset.mem_erase.mp hu
        have h : present v u:=⟨hv,us,ne.symm⟩
        have b:=lim v hv (wall v u h)
        change tag v hv (wall v u h)+(∑ j : Fin (m v),(R v).digits j l)+cellSum (R v) l (m v)<N at b
        simp only [c,dite_eq_left h,Finset.mem_range,k]
        omega
      have count:=Finset.card_le_card sub
      rw [Finset.card_range] at count
      obtain ⟨u,hu⟩:=any
      have h : present v u:=⟨hv,Finset.mem_of_mem_erase hu,(Finset.mem_erase.mp hu).1.symm⟩
      have b:=lim v hv (wall v u h)
      dsimp [k] at count ⊢
      omega
    · have empty:=Finset.not_nonempty_iff_eq_empty.mp any
      have mm : 0<m v := by
        by_contra! z
        have zero : m v=0 := by omega
        have cyc:=(R v).period
        have e:=congrArg (R v).w zero
        linarith [Real.pi_pos]
      have b:=lim v hv ⟨0,mm⟩
      simp [R58.Knockout.colors,empty,k]
      omega

end R58.AllRows
#print axioms R58.AllRows.palette
#print axioms R58.AllRows.capacity
