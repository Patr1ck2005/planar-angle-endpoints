import ClusterLimit
import JSP404.ClusterConstruction

noncomputable section
namespace R51.TwoCenters
open Filter Topology JSP404 InnerProductGeometry Real

private def wordEmbedding {r k : ℕ} (hr : r≤2^k) : Fin r ↪ BinaryWord k := by
  let e : BinaryWord k ≃ Fin (2^k) := Fintype.equivFinOfCardEq (by simp [BinaryWord])
  exact ⟨fun i => e.symm ⟨i.val,lt_of_lt_of_le i.isLt hr⟩,
    fun i j eq => Fin.ext (congrArg (fun j : Fin (2^k) => j.val) (e.symm.injective eq))⟩

private theorem tends_to_first {k : ℕ} (v : Fin (k+1)→Point) (a : BinaryWord (k+1)) :
    Tendsto (fun t : ℝ=>binaryProjection v t a) (𝓝[>] 0) (𝓝 (realDigit (a 0) • v 0)) := by
  have cont : Continuous (fun t : ℝ=>binaryProjection v t a) := by unfold binaryProjection;fun_prop
  have eq : binaryProjection v 0 a=realDigit (a 0) • v 0 := by
    unfold binaryProjection
    rw [Fin.sum_univ_succ]
    simp
  rw [←eq]
  exact cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The sharp answer on the boundary where two clusters of prescribed sizes form.
Unequal clusters can use different subsets of the same tail code. -/
theorem sharp_two_centers {r s : ℕ} (two : 2≤r) (sp : 0<s) (sr : s≤r) :
    IsLeast (attainable r s) (π-π/((Nat.clog 2 r:ℝ)+1)) := by
  classical
  refine ⟨?_,fun _ h=>least_lower two sp h⟩
  let k:=Nat.clog 2 r
  have kp : 0<k := Nat.clog_pos (by decide) (by omega)
  have fits : r≤2^k := Nat.le_pow_clog (by decide : 1<2) _
  let el:=wordEmbedding fits
  let er:=wordEmbedding (sr.trans fits)
  let wd : Labels r s→BinaryWord (k+1) := Sum.elim
    (fun i=>Fin.cons false (el i)) (fun j=>Fin.cons true (er j))
  have wi : Function.Injective wd := by
    intro i j eq
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have h : el i=el j := by funext a;simpa [wd] using congrFun eq a.succ
        rw [el.injective h]
      | inr j => simpa [wd] using congrFun eq 0
    | inr i =>
      cases j with
      | inl j => simpa [wd] using congrFun eq 0
      | inr j =>
        have h : er i=er j := by funext a;simpa [wd] using congrFun eq a.succ
        rw [er.injective h]
  let v (i : Fin (k+1)):=circleDirection ((i:ℝ)*π/(k+1:ℕ))
  have nz (i : Fin (k+1)) : v i≠0 := norm_ne_zero_iff.mp (by dsimp [v];rw [norm_circleDirection];norm_num)
  let f (t : ℝ) (i : Labels r s) := binaryProjection v t (wd i)
  have inj : ∀ᶠ t in 𝓝[>] (0:ℝ), Function.Injective (f t) := by
    filter_upwards [eventually_injective_binaryProjection v nz] with t ht
    exact ht.comp wi
  refine ⟨f,0,v 0,(nz 0).symm,?_,?_,inj,?_⟩
  · intro i
    simpa [wd,f,realDigit] using tends_to_first v (wd (Sum.inl i))
  · intro j
    simpa [wd,f,realDigit] using tends_to_first v (wd (Sum.inr j))
  · intro ε he
    let θ:=(1-1/((k+1:ℕ):ℝ))*π
    have dim : 2≤k+1 := by omega
    have positive : (0:ℝ)<((k+1:ℕ):ℝ) := by positivity
    have eqθ : θ=π-π/((Nat.clog 2 r:ℝ)+1) := by dsimp [θ,k];push_cast;ring
    have ok : 0≤θ := by
      have h : (1:ℝ)≤((k+1:ℕ):ℝ) := by exact_mod_cast (show 1≤k+1 by omega)
      exact mul_nonneg (sub_nonneg.mpr ((div_le_one positive).mpr h)) pi_pos.le
    have tri (a b c : Labels r s) : ∀ᶠ t in 𝓝[>] (0:ℝ),
        a≠b → c≠b → EuclideanGeometry.angle (f t a) (f t b) (f t c)<θ+ε := by
      by_cases ab : a=b
      · exact .of_forall (fun _ h=>(h ab).elim)
      by_cases cb : c=b
      · exact .of_forall (fun _ _ h=>(h cb).elim)
      have result := eventually_binaryProjection_angle_lt v nz ok he
        (fun i j ne x y hx hy => signed_grid_direction_angle_le_real dim ne x y hx hy)
        (wd a) (wd b) (wd c) (wi.ne ab) (wi.ne cb)
      filter_upwards [result] with t ht _ _;exact ht
    have all:=Filter.eventually_all.mpr (fun a=>Filter.eventually_all.mpr (fun b=>Filter.eventually_all.mpr (tri a b)))
    filter_upwards [inj,all] with t it ht
    have big : 3≤(configuration (f t)).card := by
      rw [configuration,Finset.card_image_of_injective _ it]
      simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
      omega
    obtain ⟨a,ha,b,hb,c,hc,ab,_,bc,high⟩:=hasLargeAngle_maxAngle big
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hc
    rw [←eqθ]
    exact high.trans_lt (ht x y z (fun h=>ab (congrArg _ h)) (fun h=>bc (congrArg _ h.symm)))

end R51.TwoCenters
#print axioms R51.TwoCenters.sharp_two_centers
