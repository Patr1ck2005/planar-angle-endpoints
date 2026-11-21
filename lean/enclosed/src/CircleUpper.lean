import RealArcSpectrum
import FourCircleCenters
import ThreeCenterStaircase

noncomputable section
namespace R59.Concyclic
open R58.CircleModel Real JSP404 R55.WeightedCollision R52.SendovCloud SendovCycle

/-- The attainable spectrum over every finite, nonsingleton family of distinct
fixed centers on a common Euclidean circle, with exactly N microscopic labels. -/
def scores (N : ℕ) : Set ℝ := {θ | ∃ t : ℕ, 2≤t ∧ ∃ c : Fin t→Point,
  Function.Injective c ∧ OnCircle c ∧ ∃w : Fin t→ℕ,(∀i,0<w i) ∧ (∑i,w i)=N ∧ θ∈attainable w c}

theorem increasing {N : ℕ} {x y : ℝ} (h : x∈scores N) (le : x≤y) : y∈scores N := by
  obtain ⟨n,m,c,inj,on,w,pos,card,hit⟩:=h
  refine ⟨n,m,c,inj,on,w,pos,card,?_⟩
  intro e ep
  obtain ⟨f,i,r,k⟩:=hit e ep
  exact ⟨f,i,r,k.trans_le (by linarith)⟩

theorem lift_onCircle {t : ℕ} (C : Lift t) : OnCircle C.centers := by
  refine ⟨C.center,C.radius,?_⟩
  intro i
  simp [Lift.centers,Lift.P,dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_pos C.pos,norm_circleDirection]

theorem equilateral : π/3∈scores 3 := by
  let lam:=2*π/3
  let a : ℕ→ℝ:=fun _=>1/2
  have lp : 0<lam := by dsimp [lam];positivity
  have total : seg a 0 3=π/lam := by
    norm_num [seg,a,lam];field_simp
    <;> ring
  obtain ⟨C,_,_,_,h⟩:=realize_arcs (t:=3) (by decide) a lp (by dsimp [lam];linarith [pi_pos])
    (fun _=>by norm_num [a]) (fun _=>rfl) total (fun _=>by norm_num [a])
  have cap:=trim (w:=fun _ : Fin 3=>1) (fun j=>Nat.one_le_pow _ _ (by decide)) h
  rw [show π-lam=π/3 by dsimp [lam];ring] at cap
  exact ⟨3,by decide,C.centers,C.centers_injective,lift_onCircle C,fun _=>1,fun _=>(Nat.zero_lt_one),by simp,cap⟩

/-- Circumcenter of the pinned isosceles Sendov triangle. The apex height is
strictly positive for every n≥2. -/
theorem sendov_onCircle {n : ℕ} (hn : 2≤n) : OnCircle (threeClusterCenters n) := by
  let z:=tan (threeClusterPhi n)
  have zp : 0<z := tan_pos_of_pos_of_lt_pi_div_two (threeClusterPhi_pos _) (threeClusterPhi_lt_half_pi hn)
  let v:=(z^2-1)/(2*z)
  let o : Point:=!₂[0,v]
  refine ⟨o,dist (threeClusterCenters n 0) o,?_⟩
  intro i
  have eq (j : Fin 3) : dist (threeClusterCenters n j) o^2=dist (threeClusterCenters n 0) o^2 := by
    fin_cases j <;> simp [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two,threeClusterCenters,o,Real.dist_eq,
      sq_abs,show tan (threeClusterPhi n)=z from rfl,v] <;> field_simp [zp.ne'] <;> ring
  nlinarith [eq i,dist_nonneg (x:=threeClusterCenters n i) (y:=o),dist_nonneg (x:=threeClusterCenters n 0) (y:=o)]

theorem low_upper {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    π-2*π/(2*(k:ℝ)+5)∈scores N := by
  let n:=k+2
  let w : Fin 3→ℕ:=![2^(k+1),2^(k+1),N-4*2^k]
  have hn : 2≤n := by dsimp [n];omega
  have wp (i) : 0<w i := by fin_cases i <;> simp [w] <;> omega
  have sz : (∑i,w i)=N := by simp [w,Fin.sum_univ_three,pow_succ];omega
  have fits (i) : w i≤2^(threeClusterDims n i) := by
    fin_cases i <;> simp [w,threeClusterDims,n] <;> omega
  refine ⟨3,by decide,threeClusterCenters n,threeClusterCenters_injective n,sendov_onCircle hn,w,wp,sz,?_⟩
  rw [←cap_source k]
  intro e ep
  have pos : 0≤angleCap k := by
    change 0≤π-2*threeClusterPhi n
    linarith [threeClusterPhi_lt_half_pi hn]
  obtain ⟨f,inj,_,near,cap⟩:=exact_weights wp fits _ (threeClusterCenters_injective n)
    (threeClusterDirections n) (threeClusterDirections_ne_zero n) pos ep ep
    (fun i j l ij _ jl=>threeClusterCenters_angle_le hn i j l ij jl.symm) (threeClusterDirections_internal hn) (threeClusterDirections_cross hn)
  exact ⟨f,inj,near,cap⟩

#print axioms equilateral
#print axioms sendov_onCircle
#print axioms low_upper
end R59.Concyclic

