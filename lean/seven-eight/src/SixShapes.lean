import BinaryFive
noncomputable section
open scoped Classical
namespace R80.Six
open Real JSP404 R55.WeightedCollision R54.Profile Finset
variable {c : Fin 6→Point} {w : Fin 6→ℕ} {θ : ℝ}

theorem low_shapes (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 4*2^k<∑i,w i) (hi : (∑i,w i)≤5*2^k)
    (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃ x : Fin 6,(∀i,dim w x≤dim w i) ∧ HalfPair k (fun j=>dim w (x.succAbove j)) := by
  obtain ⟨x,_,min⟩:=exists_min_image univ (dim w) univ_nonempty
  have least (i):dim w x≤dim w i:=min i (mem_univ _)
  obtain ⟨mass,_⟩:=low_endpoint ci wp hit lo hi bad x least
  have ang:=(R52.ThreeCover.full_staircase (N:=∑i,w i) (by have:=Nat.two_pow_pos k;omega)).unique
    (R52.ThreeCover.low_band lo hi)
  rw [ang] at bad
  refine ⟨x,least,one_unit_missing (m:=4) (fun i=>?_) mass⟩
  by_contra! big
  exact lo.not_ge (R66.Five.one_large_low_mass ci wp hit bad _ big)

theorem high_shapes (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k)
    (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃x : Fin 6,(∀i,dim w x≤dim w i) ∧ dim w x≤k ∧ HighFive k (fun j=>dim w (x.succAbove j)) := by
  classical
  obtain ⟨x,_,min⟩:=exists_min_image univ (dim w) univ_nonempty
  have least (i):dim w x≤dim w i:=min i (mem_univ _)
  obtain ⟨mass,sz⟩:=high_endpoint ci wp hit lo hi bad x least
  refine ⟨x,least,sz,?_⟩
  let d (j : Fin 5):=dim w (x.succAbove j)
  change (∑j,2^d j)=5*2^k at mass
  by_cases all : ∀j,d j≤k
  · left
    intro j
    apply le_antisymm (all j) (le_of_not_gt (fun smaller=>?_))
    have strict:=sum_lt_sum (s:=univ) (fun i _=>Nat.pow_le_pow_right (by decide : 0<2) (all i))
      ⟨j,mem_univ _,Nat.pow_lt_pow_right (by decide : 1<2) smaller⟩
    change (∑i,2^d i)<∑_i : Fin 5,2^k at strict
    simp [mass] at strict
  · push Not at all
    obtain ⟨p,large⟩:=all
    have eq:=(R52.ThreeCover.full_staircase (N:=∑i,w i) (by have:=Nat.two_pow_pos k;omega)).unique
      (R52.ThreeCover.high_band lo hi)
    have short : θ<π-π/((k:ℝ)+3):=by rwa [eq] at bad
    have kp : 0<(k:ℝ)+3:=by positivity
    have lp : 0<π-θ:=by linarith [div_pos pi_pos kp]
    have top : π<((k:ℝ)+3)*(π-θ):=by
      have t:=(div_lt_iff₀ kp).mp (show π/((k:ℝ)+3)<π-θ by linarith)
      linarith only [t]
    have dp:d p=k+1:=le_antisymm (R66.Five.individual_exponent ci wp hit lp top _) large
    have cap (j : Fin 4) : d (p.succAbove j)≤k:=by
      by_contra! many
      have one:= (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp large
      have two:= (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp many
      exact bad.not_ge (R66.Five.two_large_high ci wp hit lo hi
        (x.succAbove_right_injective.ne (Fin.succAbove_ne p j)).symm one two)
    right
    refine ⟨p,dp,one_unit_missing (m:=3) cap ?_⟩
    rw [Fin.sum_univ_succAbove (fun i=>2^d i) p,dp,pow_succ] at mass
    change (∑j : Fin 4,2^d (p.succAbove j))=3*2^k
    omega

theorem low_top {k : ℕ} (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    (lo : 9*2^k<2*(∑i,w i)) (hi : (∑i,w i)≤5*2^k) : Jsp404.alphaN (∑i,w i)≤θ := by
  by_contra! bad
  have unit:=Nat.two_pow_pos k
  obtain ⟨x,least,h⟩:=low_shapes ci wp hit (by omega) hi bad
  obtain ⟨kp,count,each⟩:=h
  change (univ.filter (fun j : Fin 5=>dim w (x.succAbove j)<k)).card=2 at count
  obtain ⟨j,hj⟩:=card_pos.mp (show 0<(univ.filter (fun j : Fin 5=>dim w (x.succAbove j)<k)).card by omega)
  have ls:dim w x<k:=(least _).trans_lt (mem_filter.mp hj).2
  have half:=Nat.pow_le_pow_right (by decide : 0<2) (show dim w x+1≤k by omega)
  rw [pow_succ] at half
  obtain ⟨mass,_⟩:=low_endpoint ci wp hit (by omega) hi bad x least
  have raw: (∑i,w i)≤∑i,2^dim w i:=sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))
  rw [Fin.sum_univ_succAbove (fun i=>2^dim w i) x] at raw
  change (∑i,w i)≤2^dim w x+fiveMass (dim w) x at raw
  omega

theorem high_top {k : ℕ} (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    (lo : 6*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) : Jsp404.alphaN (∑i,w i)≤θ := by
  by_contra! bad
  obtain ⟨x,_,min⟩:=exists_min_image univ (dim w) univ_nonempty
  obtain ⟨mass,sz⟩:=high_endpoint ci wp hit (by have:=Nat.two_pow_pos k;omega) hi bad x (fun i=>min i (mem_univ _))
  have extra:=Nat.pow_le_pow_right (by decide : 0<2) sz
  have raw: (∑i,w i)≤∑i,2^dim w i:=sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))
  rw [Fin.sum_univ_succAbove (fun i=>2^dim w i) x] at raw
  change (∑i,w i)≤2^dim w x+fiveMass (dim w) x at raw
  omega

end R80.Six
#print axioms R80.Six.low_shapes
#print axioms R80.Six.high_shapes
#print axioms R80.Six.low_top
#print axioms R80.Six.high_top