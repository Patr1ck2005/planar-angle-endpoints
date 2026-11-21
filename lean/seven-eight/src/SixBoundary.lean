import FiveCenterPublic
import FourMarkedEndpoint
import CriticalCenters
import StaircaseBands
noncomputable section
namespace R80.Six
open Real JSP404 R55.WeightedCollision R54.GapTest R54.Profile R65.Retention R56.Windows Finset

def fiveMass (d : Fin 6→ℕ) (x : Fin 6) := ∑j : Fin 5,2^(d (x.succAbove j))

theorem rounded_five_cap {c : Fin 6→Point} (ci : Function.Injective c) {w : Fin 6→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {B : ℕ} (room : 5≤B+1)
    (bad : θ<Jsp404.alphaN (B+1)) (x : Fin 6) : fiveMass (dim w) x≤B := by
  let e:=x.succAboveEmb
  let u (i : Fin 5):=2^dim w (e i)
  have up (i):0<u i:=Nat.two_pow_pos _
  have rounded:=replace_weights wp (u:=fun i=>2^dim w i) (fun _=>Nat.two_pow_pos _)
    (fun i=>exists_ne i) ci (fun _=>le_rfl) hit
  have got : θ∈attainable u (c∘e):=R58.CircleModel.restrict_attainable rounded e e.injective
  have law:=(fixed_profile up (fun i=>exists_ne i) (ci.comp e.injective)).mp got
  obtain ⟨m,R,front,back⟩:=actual_rows (c∘e) (ci.comp e.injective)
  have lo:=positive_mass_iff (ci.comp e.injective) R front back law.1
    (bad.trans (Jsp404.alphaN_lt_pi (by omega : 4≤B+1))) law.2.1
  have enough:=(lo (∑i,u i)).mp ⟨u,up,rfl,got⟩
  by_contra! full
  have many : B+1≤∑i,u i:=full
  obtain ⟨v,vp,size,att⟩:=(lo (B+1)).mpr ⟨by simpa using room,many.trans enough.2⟩
  have below:=R67.FiveCenter.lower (ci.comp e.injective) v vp att
  rw [size] at below
  exact bad.not_ge below

/-- If six rounded fibers first exceed a dyadically aligned bound while every five fit,
deleting any lightest fiber lands exactly at the bound. -/
theorem boundary_five {d : Fin 6→ℕ} {b k : ℕ} (coeff : b<8)
    (full : b*2^k<∑i,2^d i) (caps : ∀x,fiveMass d x≤b*2^k)
    (x : Fin 6) (least : ∀i,d x≤d i) :
    fiveMass d x=b*2^k ∧ d x≤k := by
  have le:=caps x
  have lower : 5*2^(d x)≤fiveMass d x := by
    calc 5*2^(d x) = ∑ _ : Fin 5,2^(d x) := by simp
         _ ≤ _ := sum_le_sum (fun j _=>Nat.pow_le_pow_right (by decide) (least (x.succAbove j)))
  have kl : d x≤k := by
    by_contra! big
    have p:=Nat.pow_le_pow_right (by decide : 0<2) (show k+1≤d x by omega)
    rw [pow_succ] at p
    have o:=Nat.mul_le_mul_right (2^k) (show b≤7 by omega)
    have positive:=Nat.two_pow_pos k
    omega
  have divB : 2^(d x)∣b*2^k := dvd_mul_of_dvd_right (pow_dvd_pow 2 kl) _
  have divL : 2^(d x)∣fiveMass d x := Finset.dvd_sum (fun j _=>pow_dvd_pow 2 (least (x.succAbove j)))
  have record := Fin.sum_univ_succAbove (fun i : Fin 6=>2^(d i)) x
  change (∑i,2^d i)=2^(d x)+fiveMass d x at record
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

theorem high_endpoint {c : Fin 6→Point} (ci : Function.Injective c) {w : Fin 6→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) (bad : θ<Jsp404.alphaN (∑i,w i))
    (x : Fin 6) (least : ∀i,dim w x≤dim w i) :
    fiveMass (dim w) x=5*2^k ∧ dim w x≤k := by
  have p:=Nat.two_pow_pos k
  have bound : θ<Jsp404.alphaN (5*2^k+1) := by
    rw [band_high (k:=k) (by omega) (by omega)]
    rwa [band_high lo hi] at bad
  exact boundary_five (by decide) (lo.trans_le (sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))))
    (rounded_five_cap ci wp hit (by omega) bound) x least

theorem low_endpoint {c : Fin 6→Point} (ci : Function.Injective c) {w : Fin 6→ℕ}
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 4*2^k<∑i,w i) (hi : (∑i,w i)≤5*2^k) (bad : θ<Jsp404.alphaN (∑i,w i))
    (x : Fin 6) (least : ∀i,dim w x≤dim w i) :
    fiveMass (dim w) x=4*2^k ∧ dim w x≤k := by
  have p:=Nat.two_pow_pos k
  have bound : θ<Jsp404.alphaN (4*2^k+1) := by
    rw [band_low (k:=k) (by omega) (by omega)]
    rwa [band_low lo hi] at bad
  exact boundary_five (by decide) (lo.trans_le (sum_le_sum (fun i _=>Nat.le_pow_clog (by decide) (w i))))
    (rounded_five_cap ci wp hit (by omega) bound) x least


end R80.Six
#print axioms R80.Six.rounded_five_cap
#print axioms R80.Six.low_endpoint
#print axioms R80.Six.high_endpoint
