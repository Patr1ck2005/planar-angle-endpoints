import CloudRounding
import Mathlib.Analysis.SpecificLimits.Basic
noncomputable section
namespace R54.Profile
open JSP404 R56.Decorated Real Filter Topology InnerProductGeometry

abbrev Labels {I : Type*} (w : I→ℕ) := (i : I) × Fin (w i)
def diagram {T : Type*} [Fintype T] (f : T→Point) := Finset.univ.image f
def Realizable {I : Type*} [Fintype I] (w : I→ℕ) (c : I→Point) (θ : ℝ) := ∀ e : ℝ,0<e →
  ∃ f : Labels w→Point, Function.Injective f ∧
    (∀ x,dist (f x) (c x.1)<e) ∧ maxAngle (diagram f)<θ+e

def rep {I : Type*} {w : I→ℕ} (pos : ∀ i,0<w i) (i : I) : Labels w := ⟨i,⟨0,pos i⟩⟩

theorem angle_lim {T : Type*} {L : Filter T} {x y : T→Point} {u v : Point} (un : u≠0) (vn : v≠0)
    (hx : Tendsto x L (𝓝 u)) (hy : Tendsto y L (𝓝 v)) :
    Tendsto (fun n=>angle (x n) (y n)) L (𝓝 (angle u v)) := by
  have h : ContinuousAt (fun z : Point×Point=>angle z.1 z.2) (u,v) := InnerProductGeometry.continuousAt_angle un vn
  exact Tendsto.comp (g:=fun z : Point×Point=>angle z.1 z.2) (f:=fun n=>(x n,y n)) h.tendsto (hx.prodMk_nhds hy)

theorem upper_limit {L : Filter ℕ} [NeBot L] {u : ℕ→ℝ} {v θ : ℝ}
    (lim : Tendsto u L (𝓝 v)) (bound : ∀ e : ℝ,0<e → ∀ᶠ n in L,u n<θ+e) : v≤θ := by
  by_contra! bad
  let e:=(v-θ)/2
  have ep : 0<e := by dsimp [e];linarith
  have small : θ+e<v := by dsimp [e];linarith
  obtain ⟨n,a,b⟩:=((tendsto_const_nhds.eventually_lt lim small).and (bound e ep)).exists
  linarith

/-- The witnesses can satisfy all viewing-cone inequalities at once. -/
theorem samples {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (pos : ∀ i,0<w i) (ci : Function.Injective c) (R : Realizable w c θ) {e : ℝ} (ep : 0<e) :
    ∃ f : Labels w→Point,Function.Injective f ∧ (∀ x,dist (f x) (c x.1)<e) ∧
      maxAngle (diagram f)<θ+e ∧ ∀ i j,i≠j → ∀ x : Fin (w i),
        angle (f (rep pos j)-f (rep pos i)) (f (rep pos j)-f ⟨i,x⟩)<e := by
  classical
  let d (m : ℕ) : ℝ:=1/((m:ℝ)+1)
  have dp (m : ℕ) : 0<d m := by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f inj near cap using fun m=>R (d m) (dp m)
  have lim (x : Labels w) : Tendsto (fun m=>f m x) atTop (𝓝 (c x.1)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _=>dist_nonneg) (fun m=>(near m x).le) dz
  have view (i j : I) (x : Fin (w i)) : ∀ᶠ n : ℕ in atTop, i≠j →
        angle (f n (rep pos j)-f n (rep pos i)) (f n (rep pos j)-f n ⟨i,x⟩)<e := by
    by_cases ne : i=j
    · exact Filter.Eventually.of_forall (fun _ h=>(h ne).elim)
    have nv:=sub_ne_zero.mpr (ci.ne (Ne.symm ne))
    have a:=angle_lim nv nv ((lim (rep pos j)).sub (lim (rep pos i))) ((lim (rep pos j)).sub (lim ⟨i,x⟩))
    change Tendsto _ _ (𝓝 (angle (c j-c i) (c j-c i))) at a
    rw [angle_self nv] at a
    exact (a.eventually_lt tendsto_const_nhds ep).mono (fun _ h _=>h)
  have all:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>Filter.eventually_all.mpr (view i j)))
  obtain ⟨n,sm,seen⟩:=((dz.eventually_lt tendsto_const_nhds ep).and all).exists
  exact ⟨f n,inj n,fun x=>(near n x).trans sm,by linarith [cap n], fun i j ne x=>seen i j x ne⟩

end R54.Profile
#print axioms R54.Profile.samples
