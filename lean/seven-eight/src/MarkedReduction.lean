import FiveDyadicBoundary
import MassStaircase
import ProfileSamples
noncomputable section
open scoped Classical
namespace R66.Five
open Real JSP404 Filter Topology InnerProductGeometry R54.Profile R55.WeightedCollision
open R53.Islands Finset

/-- In a realization of any weighted profile, each entire fiber is an isolated
marked subset for all its exterior samples, simultaneously at arbitrary aperture. -/
theorem marked_fibers {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} (ci : Function.Injective c)
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {η : ℝ} (ep : 0<η) :
    ∃ (S : Finset Point) (F : I→Finset Point) (a : I→Point),S.card=(∑i,w i) ∧ maxAngle S<θ+η ∧
      (∀i,Island S (F i) (a i) η ∧ (F i).card=w i) ∧ ∀i j,i≠j → Disjoint (F i) (F j) := by
  classical
  let d (n : ℕ):ℝ:=1/((n:ℝ)+1)
  have dp (n):0<d n:=by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose f inj near cap using fun n=>hit (d n) (dp n)
  have lim (x : Label w) : Tendsto (fun n=>f n x) atTop (𝓝 (c x.1)) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _=>dist_nonneg) (fun n=>(near n x).le) dz)
  have watch (y x : Label w) : ∀ᶠ n in atTop,y.1≠x.1 →
      angle (f n y-f n (representative wp x.1)) (f n y-f n x)<η := by
    by_cases ne : y.1=x.1
    · exact Eventually.of_forall (fun _ h=>(h ne).elim)
    have nz:=sub_ne_zero.mpr (ci.ne ne)
    have a:=angle_lim nz nz ((lim y).sub (lim (representative wp x.1))) ((lim y).sub (lim x))
    change Tendsto _ _ (𝓝 (angle (c y.1-c x.1) (c y.1-c x.1))) at a
    rw [angle_self nz] at a
    exact (a.eventually_lt tendsto_const_nhds ep).mono (fun _ h _=>h)
  obtain ⟨n,sn,view⟩:=((dz.eventually_lt tendsto_const_nhds ep).and
    (eventually_all.mpr (fun y=>eventually_all.mpr (watch y)))).exists
  let F (i : I):=univ.image (fun j : Fin (w i)=>f n ⟨i,j⟩)
  have side (i : I) (j : Fin (w i)) : f n ⟨i,j⟩∈F i:=mem_image_of_mem _ (mem_univ _)
  refine ⟨points (f n),F,fun i=>f n (representative wp i),card (inj n),by linarith [cap n],?_,?_⟩
  · intro i
    have sub : F i⊆points (f n) := by
      rintro _ he;obtain ⟨j,_,rfl⟩:=mem_image.mp he
      exact mem_image_of_mem _ (mem_univ _)
    refine ⟨⟨sub,side i _,ep.le,?_⟩,?_⟩
    · rintro _ ey _ ex
      obtain ⟨sy,ny⟩:=mem_sdiff.mp ey
      obtain ⟨y,_,rfl⟩:=mem_image.mp sy
      obtain ⟨j,_,rfl⟩:=mem_image.mp ex
      have ne : y.1≠i := by
        rcases y with ⟨u,z⟩
        rintro rfl
        exact ny (side u z)
      exact (view y ⟨i,j⟩ ne).le
    · dsimp [F]
      rw [card_image_of_injective _ (fun j k eq=>by simpa using (inj n eq)),card_univ,Fintype.card_fin]
  · intro i j ne
    apply disjoint_left.mpr
    rintro _ aa bb
    obtain ⟨u,_,rfl⟩:=mem_image.mp aa
    obtain ⟨v,_,eq⟩:=mem_image.mp bb
    exact ne (congrArg Sigma.fst (inj n eq)).symm

theorem two_large_high {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} (ci : Function.Injective c)
    (wp : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) {k : ℕ}
    (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) {i j : I} (ne : i≠j)
    (heavy : 2^k<w i) (heavy' : 2^k<w j) : Jsp404.alphaN (∑i,w i)≤θ := by
  have actual : θ∈R53.Mass.scores (∑i,w i) (R53.Mass.highClass k) := by
    intro η ep
    obtain ⟨S,F,a,sz,cap,marked,dis⟩:=marked_fibers ci wp hit ep
    exact ⟨S,sz,cap,Or.inr ⟨F i,F j,a i,a j,(marked i).1,(marked j).1,dis i j ne,
      (marked i).2 ▸ heavy,(marked j).2 ▸ heavy'⟩⟩
  have eq:=(R52.ThreeCover.full_staircase (N:=∑i,w i) (by have:=Nat.two_pow_pos k;omega)).unique
    (R52.ThreeCover.high_band lo hi)
  rw [eq]
  exact (R53.Mass.high_exact lo hi).2 actual

#print axioms marked_fibers
#print axioms two_large_high
end R66.Five