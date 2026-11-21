import HalfStep
import JSP404.ThreeClusterGeometry

noncomputable section
open scoped Classical
namespace R56.Decorated
open Real JSP404 InnerProductGeometry

/-- Binary axes at actual ordinary macrocenters, with both signs tested against
each outgoing external chord. -/
structure Axes {I : Type*} (c : I→Point) (d : I→ℕ) (θ : ℝ) where
  v : (i : I)→Fin (d i)→Point
  nonzero : ∀ i p,v i p≠0
  internal : ∀ i p q, p≠q → ∀ r s : ℝ, (r= -1 ∨ r=1) → (s= -1 ∨ s=1) →
    angle (r • v i p) (s • v i q)≤θ
  outside : ∀ i j,i≠j → ∀ p (r : ℝ), (r= -1 ∨ r=1) → angle (r • v i p) (c j-c i)≤θ

theorem alpha_lift {I : Type*} [Fintype I] {c : I→Point} (inj : Function.Injective c)
    {d : I→ℕ} {θ : ℝ} (pos : 0≤θ) (size : 3≤∑ i,2^d i)
    (centers : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ)
    (A : Axes c d θ) : alpha (∑ i,2^d i)≤θ :=
  alpha_sum_two_pow_le_of_cluster_directions c inj A.v A.nonzero pos size centers A.internal A.outside

theorem count_of_alpha {I : Type*} [Fintype I] {c : I→Point} (inj : Function.Injective c)
    {d : I→ℕ} {θ : ℝ} (pos : 0≤θ) {N : ℕ} (three : 3≤N) (lower : θ<alpha N)
    (centers : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ)
    (A : Axes c d θ) : (∑ i,2^d i)<N := by
  by_contra! big
  exact (not_lt_of_ge ((alpha_mono three big).trans (alpha_lift inj pos (three.trans big) centers A))) lower

theorem nine_and_ten (N : ℕ) (lo : 9≤N) (hi : N≤10) : alpha N=5*π/7 := by
  have h:=R42.HalfStep.alpha_when_capacity_crossed 3 N (by decide) (by omega)
    (by rw [show R42.HalfStep.halfCap 3=8 by decide];omega) (by simpa using hi)
  rw [h];norm_num;ring

theorem one_axis_count {I : Type*} [Fintype I] {c : I→Point} (inj : Function.Injective c)
    (H : Finset I) (v : I→Point) {θ : ℝ} (pos : 0≤θ) (strict : θ<5*π/7)
    (centers : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ)
    (nv : ∀ i∈H,v i≠0)
    (cross : ∀ i∈H, ∀ j,i≠j → ∀ r : ℝ, (r= -1 ∨ r=1) → angle (r • v i) (c j-c i)≤θ) :
    Fintype.card I+H.card≤8 := by
  classical
  let d (i : I) := if i∈H then 1 else 0
  have mem {i : I} (p : Fin (d i)) : i∈H := by
    by_contra h;have := p.isLt;simp [d,h] at this
  let A : Axes c d θ :=
    {v:=fun i _ => v i
     nonzero:=fun _ p => nv _ (mem p)
     internal:=by
       intro i p q ne
       have e : d i=1 := by simp [d, mem p]
       exact (ne (Fin.ext (by have h:=p.isLt;have k:=q.isLt;omega))).elim
     outside:=fun i j ne p r sg => cross i (mem p) j ne r sg}
  have bound:=count_of_alpha inj pos (N:=9) (by decide) (by rwa [nine_and_ten 9 (by decide) (by decide)]) centers A
  have eq (i : I) : (2:ℕ)^d i=1+(if i∈H then 1 else 0) := by by_cases h : i∈H <;> simp [d,h]
  simp_rw [eq] at bound
  simp [Finset.sum_add_distrib] at bound
  omega

theorem five_centers {c : Fin 5→Point} (inj : Function.Injective c)
    (H : Finset (Fin 5)) (four : 4≤H.card) (v : Fin 5→Point) {θ : ℝ} (pos : 0≤θ) (strict : θ<5*π/7)
    (centers : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ)
    (nv : ∀ i∈H,v i≠0)
    (cross : ∀ i∈H, ∀ j,i≠j → ∀ r : ℝ, (r= -1 ∨ r=1) → angle (r • v i) (c j-c i)≤θ) : False := by
  have h:=one_axis_count inj H v pos strict centers nv cross
  simp at h;omega

end R56.Decorated
#print axioms R56.Decorated.nine_and_ten
#print axioms R56.Decorated.five_centers
