import MovingEnclosure
import ProfileMinimum

noncomputable section
namespace R94.Enclosed
open JSP404 Real Filter Topology R55.WeightedCollision R89.Sharp

def marked (W : ℕ) (i : Fin 5) := if i=0 then W else 1

theorem marked_pos {W : ℕ} (wp : 0<W) (i : Fin 5) : 0<marked W i := by
  unfold marked;split <;> omega

theorem other_range {I : Type*} (c : I→Point) (i : I) :
    Set.range (fun j : {j : I // j≠i}=>c j.val)=c '' {j | j≠i} := by
  ext z
  exact ⟨fun ⟨j,h⟩=>⟨j.val,j.property,h⟩,fun ⟨j,ne,h⟩=>⟨⟨j,ne⟩,h⟩⟩

/-- On the unit ball, one margin works over the entire closed family of
separated five-site diagrams with the marked site enclosed by the others. -/
theorem normalized_gap {W : ℕ} (wp : 0<W) {ρ : ℝ} (rp : 0<ρ) :
    ∃ε : ℝ,0<ε ∧ ∀c : Fin 5→Point,(∀j,dist (c j) 0≤1) →
      (∀i j,i≠j→ρ≤dist (c i) (c j)) → c 0∈convexHull ℝ (c '' {j | j≠0}) →
      ∀θ∈attainable (marked W) c,criticalAngle W+ε≤θ := by
  classical
  by_contra! fail
  let d (n : ℕ) : ℝ:=1/((n:ℝ)+1)
  have dp (n) : 0<d n:=by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose c bound sep enc θ hit bad using fun n=>fail (d n) (dp n)
  let C : Set (Fin 5→Point):=Set.univ.pi fun _=>Metric.closedBall (0:Point) 1
  have K : IsCompact C:=isCompact_univ_pi fun _=>isCompact_closedBall (0:Point) 1
  have mem (n : ℕ) : c n∈C:=fun j _=>bound n j
  obtain ⟨b,_,f,inc,lim⟩:=K.tendsto_subseq mem
  have cv (j : Fin 5) := tendsto_pi_nhds.mp lim j
  have inj : Function.Injective b:=by
    intro i j eq
    by_contra ne
    have gap:=le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=ρ)) ((cv i).dist (cv j))
      (fun n=>sep (f n) i j ne)
    rw [eq,dist_self] at gap
    linarith
  have enclosed : b 0∈convexHull ℝ (b '' {j | j≠0}) := by
    rw [←other_range b 0]
    exact hull_limit (fun j=>cv j.val) (cv 0) (fun n=>by rw [other_range];exact enc (f n))
  have cap : criticalAngle W∈attainable (marked W) b := by
    apply attainable_limit (c:=fun n=>c (f n)) (u:=fun n=>criticalAngle W+d (f n)) cv
    · simpa using (tendsto_const_nhds (x:=criticalAngle W)).add (dz.comp inc.tendsto_atTop)
    · intro n
      exact R54.Profile.monotone (hit (f n)) (bad (f n)).le
  have all:=equality_four inj (marked_pos wp) 0 enclosed (by simpa [marked] using cap)
  norm_num at all

end R94.Enclosed
#print axioms R94.Enclosed.normalized_gap
