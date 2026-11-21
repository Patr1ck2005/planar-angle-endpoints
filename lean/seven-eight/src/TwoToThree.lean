import ThreeCoverDefs
import TwoCenterCard
noncomputable section
namespace R52.ThreeCover
open Filter Topology JSP404 Real R51.TwoCenters

theorem monotone {N : ℕ} {u v : ℝ} (hu : u∈scores N) (le : u≤v) : v∈scores N := by
  intro δ dp
  obtain ⟨S,h,lim,covered⟩:=hu δ dp
  exact ⟨S,h,by linarith,covered⟩

theorem absolute_lower {N : ℕ} (sz : 3≤N) {u : ℝ} (hu : u∈scores N) : alpha N≤u := by
  apply le_of_forall_pos_le_add
  intro ε he
  obtain ⟨S,h,up,_⟩:=hu ε he
  exact (alpha_le_maxAngle sz h).trans up.le

/-- A genuine two-center family fits in two of the three moving balls at every accuracy. -/
theorem of_two {N : ℕ} {u : ℝ} (hu : u∈byCard N) : u∈scores N := by
  classical
  obtain ⟨r,s,size,two,sp,_,f,a,b,ab,left,right,inj,angle⟩:=hu
  let i : Fin r:=⟨0,by omega⟩
  let j : Fin s:=⟨0,sp⟩
  let X : Labels r s:=Sum.inl i
  let Y : Labels r s:=Sum.inr j
  let center : Labels r s→Point:=Sum.elim (fun _=>a) (fun _=>b)
  let D:=dist a b
  have dp : 0<D := dist_pos.mpr ab
  have sep : Tendsto (fun t=>dist (f t X) (f t Y)) (𝓝[>] 0) (𝓝 D) := (left i).dist (right j)
  intro δ pos
  have lim (x : Labels r s) : Tendsto (fun t=>f t x) (𝓝[>] 0) (𝓝 (center x)) := by
    cases x with | inl i => exact left i | inr j => exact right j
  have close (x : Labels r s) : ∀ᶠ t in 𝓝[>] (0:ℝ), dist (f t x) (center x)<δ*(D/2) := by
    have l := (lim x).dist (tendsto_const_nhds (x:=center x))
    rw [dist_self] at l
    exact l.eventually_lt tendsto_const_nhds (by positivity)
  have separated : ∀ᶠ t in 𝓝[>] (0:ℝ), D/2<dist (f t X) (f t Y) :=
    tendsto_const_nhds.eventually_lt sep (by linarith)
  obtain ⟨t,it,upper,far,near⟩:=(inj.and ((angle δ pos).and (separated.and (Filter.eventually_all.mpr close)))).exists
  let S:=configuration (f t)
  have size' : S.card=N := by
    rw [show S=Finset.univ.image (f t) from rfl,Finset.card_image_of_injective _ it,Finset.card_univ]
    simpa [Labels] using size.symm
  refine ⟨S,size',upper,f t X,Finset.mem_image_of_mem _ (Finset.mem_univ _),
    f t Y,Finset.mem_image_of_mem _ (Finset.mem_univ _),dist_pos.mp (by linarith [far]),![a,b,b],?_⟩
  intro z hz
  obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hz
  have bound:dist (f t x) (center x)≤δ*dist (f t X) (f t Y) :=
    (near x).le.trans (mul_le_mul_of_nonneg_left far.le pos.le)
  cases x with
  | inl i => exact ⟨0,bound⟩
  | inr j => exact ⟨1,bound⟩

theorem high_approach {N k : ℕ} (sz : 3≤N) (cap : N≤8*2^k) :
    π-π/((k:ℝ)+3)∈scores N := by
  have dyad:=of_two (sharp_by_card sz).1
  have count : Nat.clog 2 N≤k+3 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add];norm_num;omega
  have real : (Nat.clog 2 N:ℝ)≤(k:ℝ)+3 := by exact_mod_cast count
  have pos : 0<(Nat.clog 2 N:ℝ) := by exact_mod_cast (Nat.clog_pos (by decide : 1<2) (show 1<N by omega))
  exact monotone dyad (by linarith [div_le_div_of_nonneg_left pi_pos.le pos real])

/-- All three-point configurations are covered with zero radius. -/
theorem three : IsLeast (scores 3) (alpha 3) := by
  classical
  refine ⟨?_,fun _ hu=>absolute_lower (by decide) hu⟩
  intro δ he
  obtain ⟨S,sz,bound⟩:=exists_configuration_maxAngle_lt (n:=3) (by decide) (lt_add_of_pos_right _ he)
  let e : S ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using sz)
  let c (i : Fin 3) : Point := (e.symm i).val
  obtain ⟨a,ha,b,hb,ab⟩:=Finset.one_lt_card.mp (show 1<S.card by omega)
  refine ⟨S,sz,bound,a,ha,b,hb,ab,c,?_⟩
  intro x hx
  refine ⟨e ⟨x,hx⟩,?_⟩
  simpa [c] using mul_nonneg he.le (dist_nonneg : 0≤dist a b)

end R52.ThreeCover
#print axioms R52.ThreeCover.of_two
#print axioms R52.ThreeCover.high_approach
#print axioms R52.ThreeCover.three
