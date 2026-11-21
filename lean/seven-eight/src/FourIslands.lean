import MarginFour

noncomputable section
open scoped Classical
namespace R55.FourIslands
open Real JSP404 R52.FourSeparated

def DiskCover (S : Finset Point) (δ D : ℝ) := ∃ balls : Fin 4→Point,
  ∀ x∈S, ∃ j, dist x (balls j)≤δ*D

structure Islands (S : Finset Point) (b D δ ρ : ℝ) where
  center : Fin 4→Point
  cell : Fin 4→Finset Point
  sub : ∀ i,cell i⊆S
  middle : ∀ i,center i∈cell i
  cover : ∀ x∈S, ∃ i,x∈cell i
  disjoint : ∀ i j, i≠j → Disjoint (cell i) (cell j)
  separated : ∀ i j, i≠j → b*D≤dist (center i) (center j)
  radius : ∀ i x, x∈cell i → dist (center i) x≤2*δ*D
  outside : ∀ i p, p∈S → p∉cell i → ∀ x∈cell i, dist (center i) x≤ρ*dist (center i) p
  card_sum : ∑ i,(cell i).card=S.card

theorem representatives {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S)
    {σ τ a : ℝ} (f : Four S p q σ τ) (pq : a≤dist p q) (third : a≤σ) (fourth : a≤τ) :
    ∃ v : Fin 4→Point, v 0=p ∧ v 1=q ∧ (∀ i,v i∈S) ∧
      ∀ i j, i≠j → a≤dist (v i) (v j) := by
  obtain ⟨x,xs,xp,xq,y,ys,yp,yq,yx⟩:=f
  refine ⟨![p,q,x,y],rfl,rfl,?_,?_⟩
  · intro i;fin_cases i <;> assumption
  · have px:=third.trans xp
    have qx:=third.trans xq
    have py:=fourth.trans yp.le
    have qy:=fourth.trans yq.le
    have xy:=fourth.trans yx.le
    intro i j ne
    fin_cases i <;> fin_cases j <;> first | exact (ne rfl).elim | assumption | (rw [dist_comm];assumption)

/-- The permutation sends the label of an actual representative to its ball
label in the supplied arbitrary cover. A point in several balls can be assigned
by any initial choice. -/
theorem partition {S : Finset Point} {b D δ ρ : ℝ} (dp : 0<D) (bp : 0<b)
    (ep : 0≤δ) (rp : 0<ρ) (r1 : ρ≤1) (small : 8*δ≤ρ*b)
    (v : Fin 4→Point) (mem : ∀ i,v i∈S) (sep : ∀ i j,i≠j → b*D≤dist (v i) (v j))
    (balls : Fin 4→Point) (cov : ∀ x∈S,∃ j,dist x (balls j)≤δ*D) :
    ∃ (I : Islands S b D δ ρ) (e : Fin 4≃Fin 4), I.center=v ∧
      ∀ i x,x∈I.cell i → dist x (balls (e i))≤δ*D := by
  classical
  let pick (x : Point) := if h:x∈S then Classical.choose (cov x h) else (0:Fin 4)
  have picked {x : Point} (xs : x∈S) : dist x (balls (pick x))≤δ*D := by
    simp only [pick,dite_eq_left xs];exact Classical.choose_spec (cov x xs)
  let assign := fun i => pick (v i)
  have rho_b : ρ*b≤b := by simpa using mul_le_mul_of_nonneg_right r1 bp.le
  have narrow : 2*δ*D<b*D := mul_lt_mul_of_pos_right (by linarith) dp
  have inject : Function.Injective assign := by
    intro i j eq;by_contra ne
    have h:=dist_triangle (v i) (balls (assign i)) (v j)
    have a:=picked (mem i)
    have g:=picked (mem j)
    change dist (v j) (balls (assign j))≤_ at g
    rw [←eq,dist_comm (v j)] at g
    change dist (v i) (balls (assign i))≤_ at a
    linarith [sep i j ne]
  let e := Equiv.ofBijective assign ⟨inject,Finite.injective_iff_surjective.mp inject⟩
  let label := fun x => e.symm (pick x)
  let cell := fun i => S.filter (fun x => label x=i)
  have label_v (i : Fin 4) : label (v i)=i := e.symm_apply_apply i
  have contains (i : Fin 4) : v i∈cell i := Finset.mem_filter.mpr ⟨mem i,label_v i⟩
  have ball {i : Fin 4} {x : Point} (hx : x∈cell i) : dist x (balls (e i))≤δ*D := by
    obtain ⟨xs,id⟩:=Finset.mem_filter.mp hx
    rw [←id,e.apply_symm_apply]
    exact picked xs
  have near {i : Fin 4} {x : Point} (hx : x∈cell i) :
      dist (v i) x≤2*δ*D := by
    have h:=dist_triangle (v i) (balls (e i)) x
    have g:=ball hx
    rw [dist_comm] at g
    linarith [ball (contains i)]
  have foreign (i : Fin 4) (p : Point) (ps : p∈S) (away : p∉cell i) :
      (b-2*δ)*D≤dist (v i) p := by
    have ph : p∈cell (label p) := Finset.mem_filter.mpr ⟨ps,rfl⟩
    have ne : i≠label p := by intro h;exact away (h ▸ ph)
    have t:=dist_triangle (v i) p (v (label p))
    have g:=near ph
    rw [dist_comm] at g
    linarith [sep i (label p) ne]
  have ratio : 2*δ≤ρ*(b-2*δ) := by nlinarith [mul_le_mul_of_nonneg_right r1 ep]
  refine ⟨⟨v,cell,fun _ => Finset.filter_subset _ _,contains,
    fun x xs => ⟨label x,Finset.mem_filter.mpr ⟨xs,rfl⟩⟩,?_,sep,fun _ _ hx => near hx,?_,?_⟩,
    e,rfl,fun _ _ hx => ball hx⟩
  · intro i j ne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have xi : label x=i := (Finset.mem_filter.mp hx).2
    have xj : label x=j := (Finset.mem_filter.mp hy).2
    exact ne (xi.symm.trans xj)
  · intro i p ps away x hx
    calc
      dist (v i) x ≤ 2*δ*D := near hx
      _ ≤ (ρ*(b-2*δ))*D := mul_le_mul_of_nonneg_right ratio dp.le
      _ = ρ*((b-2*δ)*D) := mul_assoc _ _ _
      _ ≤ ρ*dist (v i) p := mul_le_mul_of_nonneg_left (foreign i p ps away) rp.le
  · simpa [cell] using (Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset (Fin 4)) label)

theorem heavy {S : Finset Point} {b D δ ρ : ℝ} (I : Islands S b D δ ρ)
    {m : ℕ} (size : 4*m<S.card) : ∃ i,m<(I.cell i).card := by
  by_contra! small
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => small i)
  rw [I.card_sum] at h
  simp at h
  omega

theorem high_heavy {S : Finset Point} {b D δ ρ : ℝ} (I : Islands S b D δ ρ)
    {m : ℕ} (size : 5*m<S.card) :
    (∃ i,2*m<(I.cell i).card) ∨ ∃ i j,i≠j ∧ m<(I.cell i).card ∧ m<(I.cell j).card ∧
      Disjoint (I.cell i) (I.cell j) := by
  by_cases big : ∃ i,2*m<(I.cell i).card
  · exact Or.inl big
  right
  obtain ⟨i,hi⟩:=heavy I (m:=m) (by omega)
  by_contra! no
  have cap (j : Fin 4) : (I.cell j).card ≤ m+(if j=i then m else 0) := by
    by_cases eq : j=i
    · simp [eq];push Not at big;have h:=big i;omega
    · simp [eq];by_contra! hj
      exact no i j (Ne.symm eq) hi hj (I.disjoint i j (Ne.symm eq))
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => cap j)
  rw [I.card_sum] at h
  simp [Finset.sum_add_distrib] at h
  omega

end R55.FourIslands
#print axioms R55.FourIslands.representatives
#print axioms R55.FourIslands.partition
#print axioms R55.FourIslands.high_heavy
