import GapFormula
import CollisionAlternative
noncomputable section
namespace R54.ProfileFormula
open JSP404 Real R54.Profile R54.GapTest R55.WeightedCollision R56.Windows

private theorem fin_nontrivial {m : ℕ} (mg : 2≤m) : Nontrivial (Fin m) :=
  ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,fun eq=>Nat.zero_ne_one (congrArg Fin.val eq)⟩⟩

/-- Angle values computed from the finite lists of actual gaps and the fiber sizes,
with normalized macrocenters and no continuous axis variables. -/
def shapeValues (N : ℕ) : Set ℝ := {θ | ∃ m : ℕ,2≤m ∧ m≤N ∧ ∃ c : Fin m→Point,
  Function.Injective c ∧ Normalized c ∧ ∃ w : Fin m→ℕ,(∀ i,0<w i) ∧ (∑ i,w i)=N ∧
  ∃ a : Fin m→ℕ, ∃ R : ∀ i,Row (a i),Represents R c ∧ Witnessed R c ∧ θ=formula R c w}

theorem original_minimum {N : ℕ} (ge : 3≤N) : IsLeast (shapeValues N) (alpha N) := by
  constructor
  · obtain ⟨m,mg,le,c,ci,norm,w,hw,sz,eq,_⟩:=realized_minimum ge
    letI : Nontrivial (Fin m):=fin_nontrivial mg
    obtain ⟨a,R,front,back⟩:=actual_rows c ci
    exact ⟨m,mg,le,c,ci,norm,w,hw,sz,a,R,front,back,eq.symm.trans (minimum_eq R ci front back hw)⟩
  · rintro _ ⟨m,mg,_,c,ci,_,w,hw,sz,a,R,front,back,rfl⟩
    letI : Nontrivial (Fin m):=fin_nontrivial mg
    rw [←minimum_eq R ci front back hw]
    have h:=alpha_bound (sz.symm ▸ ge) (fixed_minimum hw (fin_other mg) ci).1.1
    rwa [sz] at h

/-- Exact residual capacity inequality. Every wall must have an actual chord as
witness and every chord must occur. It suffices to consider normalized sets with
between two and N macrocenters. -/
def CapacityObstruction (N : ℕ) (θ : ℝ) := ∃ m : ℕ,2≤m ∧ m≤N ∧ ∃ c : Fin m→Point,
  Function.Injective c ∧ Normalized c ∧ ∃ a : Fin m→ℕ, ∃ R : ∀ i,Row (a i),
    Represents R c ∧ Witnessed R c ∧ ∃ δ : ℝ,0<δ ∧ π-δ<θ ∧ 0≤π-δ ∧ Macro c (π-δ) ∧
    N≤∑ i,2^(score R i δ)

theorem capacity_iff {N : ℕ} (ge : 3≤N) {θ : ℝ} (top : θ≤π) :
    θ≤alpha N ↔ ¬CapacityObstruction N θ := by
  constructor
  · rintro lower ⟨m,mg,_,c,ci,_,a,R,front,_,δ,dp,short,pos,law,room⟩
    have cap (i j k : Fin m) (ij : i≠j) (kj : k≠j) : EuclideanGeometry.angle (c i) (c j) (c k)≤π-δ := by
      by_cases eq : i=k
      · subst k;change InnerProductGeometry.angle (c i-c j) (c i-c j)≤_
        rw [InnerProductGeometry.angle_self (sub_ne_zero.mpr (ci.ne ij))];exact pos
      · exact law i j k ij eq kj.symm
    exact (not_lt_of_ge room) (capacity_lt R dp pos ci front ge (short.trans_le lower) cap)
  · intro none
    by_contra! bad
    obtain ⟨m,mg,le,c,ci,norm,w,hw,sz,eq,axes⟩:=realized_minimum ge
    letI : Nontrivial (Fin m):=fin_nontrivial mg
    obtain ⟨a,R,front,back⟩:=actual_rows c ci
    let δ:=π-alpha N
    have dp : 0<δ := sub_pos.mpr (bad.trans_le top)
    have val : π-δ=alpha N := by dsimp [δ];ring
    have A : Admissible w c (π-δ) := val.symm ▸ axes
    obtain ⟨pos,law,digits⟩:=(admissible_iff R dp front back).mp A
    apply none
    refine ⟨m,mg,le,c,ci,norm,a,R,front,back,δ,dp,val.symm ▸ bad,pos,law,?_⟩
    rw [←sz];apply Finset.sum_le_sum
    intro i _
    exact (Nat.le_pow_clog (by decide : 1<2) (w i)).trans (Nat.pow_le_pow_right (by decide : 0<2) (digits i))

end R54.ProfileFormula
#print axioms R54.ProfileFormula.original_minimum
#print axioms R54.ProfileFormula.capacity_iff
