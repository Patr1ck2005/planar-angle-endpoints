import EndpointMass

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R62.Contraction R65.Retention

def removed {m t : ℕ} (e : Fin t↪Fin m) := univ \ univ.map e

theorem partition {m t : ℕ} (e : Fin t↪Fin m) (a : Fin m→ℕ) :
    (∑i,a i)=(∑j,a (e j))+∑i∈removed e,a i := by
  have z:=Finset.sum_sdiff (f:=a) (show univ.map e ⊆ univ from subset_univ _)
  simpa [removed,add_comm] using z.symm

variable {m : ℕ} {c : Fin m→Point} {θ : ℝ} {s : Fin m→ℕ}
  (R : ∀i,Row (s i))

/-- The simultaneous gains of all retained rows, measured in actual mass, must
be funded by the deleted sites after paying the endpoint surplus. -/
theorem deletion_budget {B v : ℕ} (full : capacity R θ=B+v) (crit : Critical c (B+1) θ)
    (below : θ<π) (front : Represents R c) {t : ℕ} (two : 2≤t) (proper : t<m)
    (e : Fin t↪Fin m) {p : Fin t→ℕ} (Q : ∀j,Row (p j))
    (fwd : Represents Q (c∘e)) (back : Witnessed Q (c∘e)) :
    v+(∑j,(mass Q θ j-mass R θ (e j))) ≤ ∑i∈removed e,mass R θ i := by
  have bound : (∑j,mass Q θ j)≤B := Nat.le_of_lt_succ (crit two proper e Q fwd back)
  have inc (j : Fin t) : mass R θ (e j)≤mass Q θ j :=
    Nat.pow_le_pow_right (by decide) (retained_row R front e Q back (sub_pos.mpr below) j)
  have eq : (∑j,mass R θ (e j))+(∑j,(mass Q θ j-mass R θ (e j)))=∑j,mass Q θ j := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun j _=>Nat.add_sub_of_le (inc j))
  have split:=partition e (mass R θ)
  change (∑i,mass R θ i)=B+v at full
  omega

/-- Multiple requested extra axes at multiple retained sites are charged jointly. -/
theorem simultaneous_charge {B v : ℕ} (full : capacity R θ=B+v) (crit : Critical c (B+1) θ)
    (below : θ<π) (front : Represents R c) {t : ℕ} (two : 2≤t) (proper : t<m)
    (e : Fin t↪Fin m) {p : Fin t→ℕ} (Q : ∀j,Row (p j))
    (fwd : Represents Q (c∘e)) (back : Witnessed Q (c∘e)) (r : Fin t→ℕ)
    (grow : ∀j,score R (e j) (π-θ)+r j≤score Q j (π-θ)) :
    v+(∑j,(2^(r j)-1)*mass R θ (e j)) ≤ ∑i∈removed e,mass R θ i := by
  apply le_trans _ (deletion_budget R full crit below front two proper e Q fwd back)
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro j _
  have inc:=Nat.pow_le_pow_right (by decide : 0<2) (grow j)
  rw [pow_add,mul_comm] at inc
  change _≤2^score Q j (π-θ)-2^score R (e j) (π-θ)
  unfold mass
  rw [Nat.sub_mul,one_mul]
  omega

theorem single_charge {B v : ℕ} (full : capacity R θ=B+v) (crit : Critical c (B+1) θ)
    (below : θ<π) (front : Represents R c) {t : ℕ} (two : 2≤t) (proper : t<m)
    (e : Fin t↪Fin m) {p : Fin t→ℕ} (Q : ∀j,Row (p j))
    (fwd : Represents Q (c∘e)) (back : Witnessed Q (c∘e)) (j : Fin t) (r : ℕ)
    (grow : score R (e j) (π-θ)+r≤score Q j (π-θ)) :
    v+(2^r-1)*mass R θ (e j)≤∑i∈removed e,mass R θ i := by
  have hit:=simultaneous_charge R full crit below front two proper e Q fwd back
    (fun k=>if k=j then r else 0) (fun k=>by
      by_cases eq:k=j
      · subst k;simpa using grow
      · simpa [eq] using retained_row R front e Q back (sub_pos.mpr below) k)
  have cost (k : Fin t) : (2^(if k=j then r else 0)-1)*mass R θ (e k)=
      if k=j then (2^r-1)*mass R θ (e j) else 0 := by by_cases eq:k=j <;> simp [eq]
  simpa only [cost,sum_ite_eq',mem_univ,ite_true] using hit

/-- If only lightest sites are removed, the required number grows exponentially
in the old score difference and in the number of additional axes. -/
theorem light_count {B : ℕ} (x : Fin m) (least : ∀i,score R x (π-θ)≤score R i (π-θ))
    (full : capacity R θ=B+mass R θ x) (crit : Critical c (B+1) θ)
    (below : θ<π) (front : Represents R c) {t : ℕ} (two : 2≤t) (proper : t<m)
    (e : Fin t↪Fin m) (light : ∀i∈removed e,mass R θ i=mass R θ x)
    {p : Fin t→ℕ} (Q : ∀j,Row (p j)) (fwd : Represents Q (c∘e)) (back : Witnessed Q (c∘e))
    (j : Fin t) (r : ℕ) (grow : score R (e j) (π-θ)+r≤score Q j (π-θ)) :
    1+(2^r-1)*2^(score R (e j) (π-θ)-score R x (π-θ))≤(removed e).card := by
  have charge:=single_charge R full crit below front two proper e Q fwd back j r grow
  have del : (∑i∈removed e,mass R θ i)=(removed e).card*mass R θ x := by
    calc _=∑_i∈removed e,mass R θ x := sum_congr rfl light
         _=_ := by simp
  have fac : mass R θ (e j)=2^(score R (e j) (π-θ)-score R x (π-θ))*mass R θ x := by
    unfold mass
    rw [←pow_add,Nat.sub_add_cancel (least _)]
  rw [del,fac] at charge
  apply Nat.le_of_mul_le_mul_right _ (show 0<mass R θ x from pow_pos (by decide) _)
  simpa only [add_mul,one_mul,mul_assoc] using charge

end R85.CriticalMass
#print axioms R85.CriticalMass.deletion_budget
#print axioms R85.CriticalMass.simultaneous_charge
#print axioms R85.CriticalMass.single_charge
#print axioms R85.CriticalMass.light_count
