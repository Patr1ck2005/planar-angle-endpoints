import RetainedGains

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R62.Contraction R65.Retention

abbrev mass {I : Type*} {m : I→ℕ} (R : ∀i,Row (m i)) (θ : ℝ) (i : I) :=
  (2:ℕ)^score R i (π-θ)

variable {h : ℕ} {c : Fin (h+1)→Point} {θ : ℝ}
    {m : Fin (h+1)→ℕ} (R : ∀i,Row (m i))

/-- The conclusion holds for any positive integral coefficient b with at
least b survivors after deleting a single site. The endpoint applications
use b=4 and b=5. -/
theorem endpoint {b k : ℕ} (two : 2≤h) (enough : b≤h) (ci : Function.Injective c)
    (below : θ<π) (front : Represents R c) (room : b*2^k+1≤capacity R θ)
    (crit : Critical c (b*2^k+1) θ) (x : Fin (h+1))
    (least : ∀i,score R x (π-θ)≤score R i (π-θ)) :
    score R x (π-θ)≤k ∧ mass R θ x ∣ b*2^k ∧ capacity R θ=b*2^k+mass R θ x := by
  classical
  let : Nontrivial (Fin h) := Fintype.one_lt_card_iff_nontrivial.mp (by simp;omega)
  obtain ⟨s,Q,forward,back⟩:=actual_rows (c∘x.succAboveEmb) (ci.comp x.succAboveEmb.injective)
  have oldnew (i : Fin h) : mass R θ (x.succAbove i)≤mass Q θ i :=
    Nat.pow_le_pow_right (by decide) (retained_row R front x.succAboveEmb Q back (sub_pos.mpr below) i)
  have cap : (∑i,mass R θ (x.succAbove i))≤b*2^k :=
    (sum_le_sum (s:=univ) (fun i _=>oldnew i)).trans (Nat.le_of_lt_succ (crit two (by omega) _ Q forward back))
  have all (i : Fin (h+1)) : mass R θ x≤mass R θ i := Nat.pow_le_pow_right (by decide) (least i)
  have lower : h*mass R θ x≤∑i,mass R θ (x.succAbove i) := by
    simpa using sum_le_sum (s:=univ) (fun i _=>all (x.succAbove i))
  have mk : mass R θ x≤2^k := Nat.le_of_mul_le_mul_left
    ((lower.trans cap).trans (Nat.mul_le_mul_right _ enough)) (by omega)
  have sk : score R x (π-θ)≤k := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp mk
  have dv : mass R θ x∣b*2^k := dvd_mul_of_dvd_right (pow_dvd_pow 2 sk) b
  have df : mass R θ x∣capacity R θ := Finset.dvd_sum (fun i _=>pow_dvd_pow 2 (least i))
  have dd := Nat.dvd_sub df dv
  have pos : 0<capacity R θ-b*2^k := by omega
  have gap := Nat.le_of_dvd pos dd
  have full : capacity R θ=mass R θ x+∑i,mass R θ (x.succAbove i) := Fin.sum_univ_succAbove _ x
  exact ⟨sk,dv,by omega⟩

/-- Removing any lightest site leaves exactly the previous capacities and
retains the endpoint mass B. -/
theorem light_deletion {b k : ℕ} (two : 2≤h) (enough : b≤h) (ci : Function.Injective c)
    (below : θ<π) (front : Represents R c) (room : b*2^k+1≤capacity R θ)
    (crit : Critical c (b*2^k+1) θ) (x : Fin (h+1))
    (least : ∀i,score R x (π-θ)≤score R i (π-θ))
    {s : Fin h→ℕ} (Q : ∀i,Row (s i)) (fwd : Represents Q (c∘x.succAboveEmb))
    (back : Witnessed Q (c∘x.succAboveEmb)) :
    capacity Q θ=b*2^k ∧ ∀j,score Q j (π-θ)=score R (x.succAbove j) (π-θ) := by
  have st (j : Fin h) : score Q j (π-θ)=score R (x.succAbove j) (π-θ) :=
    le_antisymm (le_of_not_gt (fun gt=>(least _).not_gt
      (deletion_gain_lt R two below front room crit x Q fwd back j gt)))
      (retained_row R front _ Q back (sub_pos.mpr below) j)
  have tot:=(endpoint R two enough ci below front room crit x least).2.2
  have split : capacity R θ=mass R θ x+∑i,mass R θ (x.succAbove i) := Fin.sum_univ_succAbove _ x
  refine ⟨?_,st⟩
  change (∑j,mass Q θ j)=_
  simp only [mass,st] at *
  omega

def one_light {I : Type*} [DecidableEq I] {m : I→ℕ} (R : ∀i,Row (m i)) (θ : ℝ) (x i : I) : ℕ :=
  if i=x then 1 else mass R θ i

/-- One actual positive weighting of the endpoint has a single designated unit
fiber and saturates every other site. -/
theorem endpoint_weighting {b k : ℕ} (two : 2≤h) (enough : b≤h) (ci : Function.Injective c)
    (pos : 0≤θ) (below : θ<π) (mac : Macro c θ) (front : Represents R c) (back : Witnessed R c)
    (room : b*2^k+1≤capacity R θ) (crit : Critical c (b*2^k+1) θ) (x : Fin (h+1))
    (least : ∀i,score R x (π-θ)≤score R i (π-θ)) :
    (∑i,one_light R θ x i)=b*2^k+1 ∧ θ∈attainable (one_light R θ x) c := by
  have tot:=(endpoint R two enough ci below front room crit x least).2.2
  have split : capacity R θ=mass R θ x+∑i,mass R θ (x.succAbove i) := Fin.sum_univ_succAbove _ x
  constructor
  · rw [Fin.sum_univ_succAbove _ x]
    simp only [one_light,ite_true,Fin.succAbove_ne,ite_false];omega
  · let : Nontrivial (Fin (h+1)) := Fintype.one_lt_card_iff_nontrivial.mp (by simp;omega)
    apply (fits_iff ci R front back pos below mac (w:=one_light R θ x) (fun i=>by
      unfold one_light;split <;> positivity)).mpr
    intro i;unfold one_light;split
    · exact Nat.one_le_pow _ _ (by decide)
    · exact le_rfl

end R85.CriticalMass
#print axioms R85.CriticalMass.endpoint
#print axioms R85.CriticalMass.light_deletion
#print axioms R85.CriticalMass.endpoint_weighting
