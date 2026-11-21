import MultipleAnchors
import JSP404.ClassicalBounds

noncomputable section
namespace R51.TwoCenters
open Real Filter Topology JSP404 InnerProductGeometry R51.Anchored

def configuration {I : Type*} [Fintype I] (f : I→Point) : Finset Point := Finset.univ.image f

/-- Any net of genuine finite configurations with a cloud converging to c and an external label
converging to a different point d. The upper hypothesis is precisely a limsup bound. -/
theorem cluster_limit_budget {I T : Type*} [Fintype I] [DecidableEq I] {L : Filter T} [NeBot L]
    (f : T→I→Point) (F : Finset I) (two : 2≤F.card) (p : I) (out : p∉F)
    {c d : Point} (cd : c≠d) (cloud : ∀ i∈F,Tendsto (fun t=>f t i) L (𝓝 c))
    (anchor : Tendsto (fun t=>f t p) L (𝓝 d))
    (inj : ∀ᶠ t in L, Function.Injective (f t)) {u : ℝ}
    (cap : ∀ ε : ℝ, 0<ε → ∀ᶠ t in L, maxAngle (configuration (f t))<u+ε) :
    ((Nat.clog 2 F.card : ℝ)+1)*(π-u)≤π := by
  classical
  let v:=d-c
  have vn : v≠0 := sub_ne_zero.mpr cd.symm
  let k : ℝ := (Nat.clog 2 F.card:ℝ)+1
  have kp : 0<k := by dsimp [k];positivity
  have est (ε : ℝ) (he : 0<ε) : k*(π-u)≤π+(k+2)*ε := by
    have one (i : F) : ∀ᶠ t in L, angle v (f t p-f t i)<ε := by
      have pair : Tendsto (fun t => (v,f t p-f t i)) L (𝓝 (v,v)) :=
        tendsto_const_nhds.prodMk_nhds (anchor.sub (cloud i i.property))
      have ang := (InnerProductGeometry.continuousAt_angle (x:=(v,v)) vn vn).tendsto.comp pair
      change Tendsto (fun t=>angle v (f t p-f t i)) L (𝓝 (angle v v)) at ang
      rw [angle_self vn] at ang
      exact ang.eventually_lt tendsto_const_nhds he
    obtain ⟨t,it,ct,atmost⟩ := (inj.and ((Filter.eventually_all.mpr one).and (cap ε he))).exists
    let S:=configuration (f t)
    let A:=F.image (f t)
    have size : A.card=F.card := Finset.card_image_of_injective F it
    have sub : A⊆S := Finset.image_subset_image (Finset.subset_univ F)
    have mem : f t p∈S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have ext : f t p∉A := by
      intro h
      obtain ⟨i,hi,e⟩:=Finset.mem_image.mp h
      exact out (it e ▸ hi)
    have cone : InCone A (f t p) v ε := by
      intro x hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
      exact (ct ⟨i,hi⟩).le
    have h:=anchored_budget sub (size.symm ▸ two) mem ext vn he.le cone
    rw [size] at h
    change k*(π-maxAngle S)≤_ at h
    change maxAngle S<u+ε at atmost
    nlinarith [mul_lt_mul_of_pos_left atmost kp]
  by_contra! bad
  change π<k*(π-u) at bad
  let e:=(k*(π-u)-π)/(2*(k+2))
  have hs : 0<2*(k+2) := by positivity
  have ep : 0<e := div_pos (sub_pos.mpr bad) hs
  have eq : e*(2*(k+2))=k*(π-u)-π := div_mul_cancel₀ _ hs.ne'
  nlinarith [est e ep]

abbrev Labels (r s : ℕ) := Sum (Fin r) (Fin s)

/-- Upper limits at the stratum with two distinct macroscopic centers and specified multiplicities.
The definition fixes neither internal scales nor any relation between the two clouds. -/
def attainable (r s : ℕ) : Set ℝ := {u | ∃ f : ℝ→Labels r s→Point, ∃ c d : Point, c≠d ∧
  (∀ i, Tendsto (fun t=>f t (.inl i)) (𝓝[>] 0) (𝓝 c)) ∧
  (∀ j, Tendsto (fun t=>f t (.inr j)) (𝓝[>] 0) (𝓝 d)) ∧
  (∀ᶠ t in 𝓝[>] 0, Function.Injective (f t)) ∧
  ∀ ε : ℝ, 0<ε → ∀ᶠ t in 𝓝[>] 0, maxAngle (configuration (f t))<u+ε}

theorem least_lower {r s : ℕ} (two : 2≤r) (sp : 0<s) {u : ℝ} (hu : u∈attainable r s) :
    π-π/((Nat.clog 2 r : ℝ)+1)≤u := by
  classical
  obtain ⟨f,c,d,cd,left,right,inj,cap⟩:=hu
  let F : Finset (Labels r s) := Finset.univ.image Sum.inl
  have size : F.card=r := by simp [F,Finset.card_image_of_injective _ Sum.inl_injective]
  let j : Fin s := ⟨0,sp⟩
  have out : (Sum.inr j : Labels r s)∉F := by simp [F]
  have cloud (x : Labels r s) (hx : x∈F) : Tendsto (fun t=>f t x) (𝓝[>] 0) (𝓝 c) := by
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact left i
  have bound:=cluster_limit_budget f F (size.symm ▸ two) (Sum.inr j) out cd cloud (right j) inj cap
  rw [size,mul_comm] at bound
  have kp : (0:ℝ)<(Nat.clog 2 r:ℝ)+1 := by positivity
  linarith [(le_div_iff₀ kp).mpr bound]

end R51.TwoCenters
#print axioms R51.TwoCenters.cluster_limit_budget
#print axioms R51.TwoCenters.least_lower
