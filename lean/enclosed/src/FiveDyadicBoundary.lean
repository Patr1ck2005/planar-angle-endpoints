import CriticalCenters
import StaircaseBands
noncomputable section
namespace R66.Five
open Real JSP404 R55.WeightedCollision R54.GapTest R54.Profile R65.Retention R56.Windows Finset

def fourMass (d : Fin 5→ℕ) (x : Fin 5) := ∑j : Fin 4,2^(d (x.succAbove j))

theorem rounded_four_cap {c : Fin 5→Point} (ci : Function.Injective c) {w : Fin 5→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {B : ℕ} (room : 4≤B+1)
    (bad : θ<Jsp404.alphaN (B+1)) (x : Fin 5) : fourMass (dim w) x≤B := by
  let e:=x.succAboveEmb
  let u (i : Fin 4):=2^dim w (e i)
  have up (i):0<u i:=Nat.two_pow_pos _
  have rounded:=replace_weights wp (u:=fun i=>2^dim w i) (fun _=>Nat.two_pow_pos _)
    (fun i=>exists_ne i) ci (fun _=>le_rfl) hit
  have got : θ∈attainable u (c∘e):=R58.CircleModel.restrict_attainable rounded e e.injective
  have law:=(fixed_profile up (fun i=>exists_ne i) (ci.comp e.injective)).mp got
  obtain ⟨m,R,front,back⟩:=actual_rows (c∘e) (ci.comp e.injective)
  have lo:=positive_mass_iff (ci.comp e.injective) R front back law.1
    (bad.trans (Jsp404.alphaN_lt_pi room)) law.2.1
  have enough:=(lo (∑i,u i)).mp ⟨u,up,rfl,got⟩
  by_contra! full
  have many : B+1≤∑i,u i:=full
  obtain ⟨v,vp,size,att⟩:=(lo (B+1)).mpr ⟨by simpa using room,many.trans enough.2⟩
  have below:=(R53.FourCover.full_staircase (N:=B+1) (by omega)).2
    (size ▸ R59.Concyclic.four_scores (by decide) (by decide) (c∘e) (ci.comp e.injective) vp att)
  exact bad.not_ge below

/-- If five rounded fibers first exceed a dyadically aligned bound while every four fit,
deleting any lightest fiber lands exactly at the bound. -/
theorem boundary_four {d : Fin 5→ℕ} {b k : ℕ} (coeff : b<8)
    (full : b*2^k<∑i,2^d i) (caps : ∀x,fourMass d x≤b*2^k)
    (x : Fin 5) (least : ∀i,d x≤d i) :
    fourMass d x=b*2^k ∧ d x≤k := by
  have le:=caps x
  have lower : 4*2^(d x)≤fourMass d x := by
    calc 4*2^(d x) = ∑ _ : Fin 4,2^(d x) := by simp
         _ ≤ _ := sum_le_sum (fun j _=>Nat.pow_le_pow_right (by decide) (least (x.succAbove j)))
  have kl : d x≤k := by
    by_contra! big
    have p:=Nat.pow_le_pow_right (by decide : 0<2) (show k+1≤d x by omega)
    rw [pow_succ] at p
    have o:=Nat.mul_le_mul_right (2^k) (show b≤7 by omega)
    have positive:=Nat.two_pow_pos k
    omega
  have divB : 2^(d x)∣b*2^k := dvd_mul_of_dvd_right (pow_dvd_pow 2 kl) _
  have divL : 2^(d x)∣fourMass d x := Finset.dvd_sum (fun j _=>pow_dvd_pow 2 (least (x.succAbove j)))
  have record := Fin.sum_univ_succAbove (fun i : Fin 5=>2^(d i)) x
  change (∑i,2^d i)=2^(d x)+fourMass d x at record
  refine ⟨le_antisymm le (le_of_not_gt ?_),kl⟩
  intro strict
  have gap:=Nat.le_of_dvd (Nat.sub_pos_of_lt strict) (Nat.dvd_sub divB divL)
  omega

private theorem band_high {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    Jsp404.alphaN N=π-π/((k:ℝ)+3) :=
  (R52.ThreeCover.full_staircase (by have:=Nat.two_pow_pos k;omega : 3≤N)).unique
    (R52.ThreeCover.high_band lo hi)

private theorem band_low {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    Jsp404.alphaN N=π-2*π/(2*(k:ℝ)+5) :=
  (R52.ThreeCover.full_staircase (by have:=Nat.two_pow_pos k;omega : 3≤N)).unique
    (R52.ThreeCover.low_band lo hi)

theorem high_endpoint {c : Fin 5→Point} (ci : Function.Injective c) {w : Fin 5→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) (bad : θ<Jsp404.alphaN (∑i,w i))
    (x : Fin 5) (least : ∀i,dim w x≤dim w i) :
    fourMass (dim w) x=5*2^k ∧ dim w x≤k := by
  have p:=Nat.two_pow_pos k
  have bound : θ<Jsp404.alphaN (5*2^k+1) := by
    rw [band_high (k:=k) (by omega) (by omega)]
    rwa [band_high lo hi] at bad
  exact boundary_four (by decide) (lo.trans_le (sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))))
    (rounded_four_cap ci wp hit (by omega) bound) x least

theorem low_endpoint {c : Fin 5→Point} (ci : Function.Injective c) {w : Fin 5→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 4*2^k<∑i,w i) (hi : (∑i,w i)≤5*2^k) (bad : θ<Jsp404.alphaN (∑i,w i))
    (x : Fin 5) (least : ∀i,dim w x≤dim w i) :
    fourMass (dim w) x=4*2^k ∧ dim w x≤k := by
  have p:=Nat.two_pow_pos k
  have bound : θ<Jsp404.alphaN (4*2^k+1) := by
    rw [band_low (k:=k) (by omega) (by omega)]
    rwa [band_low lo hi] at bad
  exact boundary_four (by decide) (lo.trans_le (sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))))
    (rounded_four_cap ci wp hit (by omega) bound) x least

theorem upper_high_band {c : Fin 5→Point} (ci : Function.Injective c) {w : Fin 5→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 6*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) :
    Jsp404.alphaN (∑i,w i)≤θ := by
  by_contra! bad
  obtain ⟨x,_,least⟩:=Finset.exists_min_image univ (dim w) univ_nonempty
  obtain ⟨eq,sz⟩:=high_endpoint ci wp hit (by omega) hi bad x (fun i=>least i (mem_univ _))
  have p:=Nat.pow_le_pow_right (by decide : 0<2) sz
  have sum:=Fin.sum_univ_succAbove (fun i : Fin 5=>2^dim w i) x
  change (∑i,2^dim w i)=2^dim w x+fourMass (dim w) x at sum
  have le : (∑i,w i)≤∑i,2^dim w i :=sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))
  omega

#print axioms rounded_four_cap
#print axioms low_endpoint
#print axioms high_endpoint
#print axioms upper_high_band
end R66.Five