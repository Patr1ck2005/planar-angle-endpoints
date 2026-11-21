import WeightedConstruction

noncomputable section
namespace R55.WeightedCollision
open Real Filter Topology JSP404

variable {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}

/-- The shared unit-axis condition in finite dimensions dᵢ=clog₂(wᵢ). -/
def Admissible (w : I→ℕ) (c : I→Point) (θ : ℝ) : Prop :=
  0≤θ ∧ Macro c θ ∧ ∃ v : (i : I)→Fin (dim w i)→Point,
    (∀ i j, ‖v i j‖=1) ∧ Internal v θ ∧ External c v θ

/-- The same axes realize every positive vector of fiber cardinalities
that fits their capacities. -/
theorem transfer {u : I→ℕ} (hu : ∀ i, 0<u i) (fits : ∀ i, u i≤2^(dim w i))
    (hc : Function.Injective c) (axes : Admissible w c θ) : θ∈attainable u c := by
  obtain ⟨hθ,outer,v,unit,internal,ext⟩ := axes
  have vn (i) (j) : v i j≠0 := by intro eq; have := unit i j; simp [eq] at this
  intro ε he
  obtain ⟨f,inj,_,rad,cap⟩ := exact_weights hu fits c hc v vn hθ he he outer internal ext
  exact ⟨f,inj,rad,cap⟩

theorem admissible_mem (hw : ∀ i, 0<w i) (hc : Function.Injective c)
    (axes : Admissible w c θ) : θ∈attainable w c :=
  transfer hw (fun i=>Nat.le_pow_clog (by decide : 1<2) (w i)) hc axes

/-- In particular one can fill each fiber to the next exact power of two
at the identical tolerance and with the same macroscopic centers. -/
theorem binary_roundup (hc : Function.Injective c) (axes : Admissible w c θ) :
    θ∈attainable (fun i=>2^(dim w i)) c :=
  transfer (fun _=>pow_pos (by decide) _) (fun _=>le_rfl) hc axes

/-- A single sequence of exact-size configurations, fixing every representative,
with every cloud shrinking and the limsup of actual maximum angles at most θ. -/
theorem fixed_sequence (hw : ∀ i, 0<w i) (hc : Function.Injective c)
    (axes : Admissible w c θ) :
    ∃ f : ℕ→Label w→Point, (∀ n, Function.Injective (f n)) ∧
      (∀ n i, f n (representative hw i)=c i) ∧
      (∀ a, Tendsto (fun n=>f n a) atTop (𝓝 (c a.1))) ∧
      (∀ n, (points (f n)).card=∑ i,w i) ∧
      ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, maxAngle (points (f n))<θ+ε := by
  obtain ⟨hθ,outer,v,unit,internal,ext⟩ := axes
  have vn (i) (j) : v i j≠0 := by intro eq; have := unit i j; simp [eq] at this
  let r (n : ℕ) := 1/((n:ℝ)+1)
  have pos (n : ℕ) : 0<r n := by dsimp [r]; positivity
  have lim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f inj rep rad cap using fun n=> exact_weights hw
    (fun i=>Nat.le_pow_clog (by decide : 1<2) (w i)) c hc v vn hθ (pos n) (pos n) outer internal ext
  refine ⟨f,inj,rep,?_,fun n=>card (inj n),?_⟩
  · intro a
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _=>dist_nonneg) (fun n=>(rad n a).le) lim
  · intro ε he
    exact (lim.eventually_lt tendsto_const_nhds he).mono (fun n h=>by linarith [cap n])

#print axioms transfer
#print axioms admissible_mem
#print axioms binary_roundup
#print axioms fixed_sequence
end R55.WeightedCollision
