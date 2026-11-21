import MarginFour
import ThreeCoverDefs
noncomputable section
namespace R52.ThreeCover
open JSP404 Real R52.FourSeparated

/-- Four separated points cannot lie in three balls of a given common radius. -/
theorem packing {p q : Point} {S : Finset Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {a b δ : ℝ} (a1 : a≤1) (ba : b<a) (small : 2*δ≤b)
    (four : Four S p q (a*dist p q) (b*dist p q)) (c : Fin 3→Point)
    (cover : ∀ x∈S, ∃ i, dist x (c i)≤δ*dist p q) : False := by
  classical
  let D:=dist p q
  have dp : 0<D := dist_pos.mpr pq
  obtain ⟨x,hx,xp,xq,y,hy,yp,yq,yx⟩:=four
  have st : b*D<a*D := mul_lt_mul_of_pos_right ba dp
  have ap : a*D≤D := by simpa using mul_le_mul_of_nonneg_right a1 dp.le
  have dist01 : b*D<dist p q := st.trans_le ap
  have dist02 : b*D<dist p x := by rw [dist_comm];exact st.trans_le xp
  have dist12 : b*D<dist q x := by rw [dist_comm];exact st.trans_le xq
  let z : Fin 4→Point := ![p,q,x,y]
  have inside (i : Fin 4) : z i∈S := by fin_cases i <;> assumption
  have d10 : b*D<dist q p := by rwa [dist_comm]
  have d20 : b*D<dist x p := st.trans_le xp
  have d21 : b*D<dist x q := st.trans_le xq
  have d03 : b*D<dist p y := by rw [dist_comm];exact yp
  have d13 : b*D<dist q y := by rw [dist_comm];exact yq
  have d23 : b*D<dist x y := by rw [dist_comm];exact yx
  have apart (i j : Fin 4) (ne : i≠j) : b*D<dist (z i) (z j) := by
    fin_cases i <;> fin_cases j <;> first | exact (ne rfl).elim | assumption
  choose tag ct using fun i=>cover (z i) (inside i)
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have steps := dist_triangle (z i) (c (tag i)) (z j)
    have tail : dist (c (tag i)) (z j)≤δ*D := by rw [eq,dist_comm];exact ct j
    have h := mul_le_mul_of_nonneg_right small dp.le
    nlinarith [apart i j ne,ct i]
  have impossible:=Fintype.card_le_of_injective tag inj
  norm_num at impossible

private theorem lower {N : ℕ} {θ : ℝ}
    (excludes : ∀ ε : ℝ, 0<ε → ∃ a b : ℝ, a≤1 ∧ 0<b ∧ b<a ∧
      ∀ (S : Finset Point), S.card=N → maxAngle S≤θ-ε →
      ∀ p∈S, ∀ q∈S, p≠q → Four S p q (a*dist p q) (b*dist p q))
    {u : ℝ} (hu : u∈scores N) : θ≤u := by
  by_contra! wrong
  let e:=(θ-u)/2
  have ep : 0<e := by dsimp [e];linarith
  obtain ⟨a,b,a1,bp,ba,four⟩:=excludes e ep
  let δ:=min e (b/4)
  have dp : 0<δ := lt_min ep (by positivity)
  obtain ⟨S,size,cap,p,hp,q,hq,pq,c,cover⟩:=hu δ dp
  have angle : maxAngle S≤θ-e := by have := min_le_left e (b/4);dsimp [δ,e] at *;linarith
  have small : 2*δ≤b := by have := min_le_right e (b/4);dsimp [δ];linarith
  exact packing hp hq pq a1 ba small (four S size angle p hp q hq pq) c cover

private theorem ratios {φ η : ℝ} (ph : 0<φ) (ph' : φ<π) (eh : 0<η) (eh' : η<π/2) :
    sin φ≤1 ∧ 0<sin η*sin φ ∧ sin η*sin φ<sin φ := by
  have p:=sin_pos_of_pos_of_lt_pi ph ph'
  have e:=sin_pos_of_pos_of_lt_pi eh (eh'.trans (by linarith [pi_pos]))
  have sm : sin η<1 := by
    simpa using Real.sin_lt_sin_of_lt_of_le_pi_div_two (show -(π/2)≤η by linarith [pi_pos]) (le_refl (π/2)) eh'
  exact ⟨sin_le_one _,mul_pos e p,by simpa using mul_lt_mul_of_pos_right sm p⟩

/-- Full lower staircase on every cardinality above each threshold for configurations
coverable by any three disks of vanishing diameter-relative radius. -/
theorem low_bound {N k : ℕ} (sz : 4*2^k<N) {u : ℝ} (hu : u∈scores N) :
    π-2*π/(2*(k:ℝ)+5)≤u := by
  apply lower (N:=N) (u:=u) _ hu
  intro e ep
  obtain ⟨ph,ph',eh,eh'⟩:=lower_separation k ep
  obtain ⟨a,b,c⟩:=ratios ph ph' eh eh'
  refine ⟨_,_,a,b,c,?_⟩
  intro S card ang p hp q hq pq
  simpa only [mul_assoc] using low_margin hp hq pq (card.symm ▸ sz) ep ang

theorem high_bound {N k : ℕ} (sz : 5*2^k<N) {u : ℝ} (hu : u∈scores N) :
    π-π/((k:ℝ)+3)≤u := by
  apply lower (N:=N) (u:=u) _ hu
  intro e ep
  obtain ⟨ph,ph',eh,eh'⟩:=upper_separation k ep
  obtain ⟨a,b,c⟩:=ratios ph ph' eh eh'
  refine ⟨_,_,a,b,c,?_⟩
  intro S card ang p hp q hq pq
  simpa only [mul_assoc] using high_margin hp hq pq (card.symm ▸ sz) ep ang

end R52.ThreeCover
#print axioms R52.ThreeCover.low_bound
#print axioms R52.ThreeCover.high_bound
