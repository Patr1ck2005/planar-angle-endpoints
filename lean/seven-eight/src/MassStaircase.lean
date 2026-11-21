import MassTwoCenters
import FourCenterStaircase
noncomputable section
namespace R53.Mass
open JSP404 R53.Islands R52.TwoAnchor Real

private theorem bound {N k : ℕ} {P : Finset Point→ℝ→Prop} {u θ : ℝ} (hu : u∈scores N P)
    (stability : ∀ (S : Finset Point),S.card=N → ∀ e,0<e → maxAngle S≤θ-e →
      ∀ η,P S η → ((k:ℝ)+3)*e≤4*η) : θ≤u := by
  by_contra! wrong
  let e:=(θ-u)/2
  have ep : 0<e := by dsimp [e];linarith
  let η:=min e (((k:ℝ)+3)*e/8)
  have pos : 0<η := lt_min ep (by positivity)
  obtain ⟨S,sz,lim,cl⟩:=hu η pos
  have le : η≤e := min_le_left _ _
  have cap : maxAngle S≤θ-e := by dsimp [e] at *;linarith
  have v:=stability S sz e ep cap η cl
  have upper : η≤((k:ℝ)+3)*e/8 := min_le_right _ _
  linarith [mul_pos (show 0<(k:ℝ)+3 by positivity) ep]

theorem low_exact {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    IsLeast (scores N (lowClass k)) (π-2*π/(2*(k:ℝ)+5)) := by
  refine ⟨low_witness lo hi,?_⟩
  intro u hu
  apply bound (k:=k) hu
  rintro S sz e ep cap η ⟨F,a,I,ext,big⟩
  exact low_stability I ext (sz.symm ▸ lo) big ep.le cap

theorem high_exact {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    IsLeast (scores N (highClass k)) (π-π/((k:ℝ)+3)) := by
  refine ⟨high_witness lo hi,?_⟩
  intro u hu
  apply bound (k:=k) hu
  rintro S sz e ep cap η (⟨F,a,I,ext,big⟩|⟨F,H,a,b,I,J,disj,big,big'⟩)
  · have upper:=oversize I ext big
    let B:=(k:ℝ)+3
    have bp : 0<B := by dsimp [B];positivity
    have d : π/B+e≤defect S := by dsimp [B,defect];linarith
    have x:=mul_le_mul_of_nonneg_left d bp.le
    rw [mul_add,show B*(π/B)=π by field_simp] at x
    change B*defect S≤_ at upper
    change B*e≤_
    linarith [I.pos]
  · exact high_stability I J disj (sz.symm ▸ lo) big big' cap

/-- The score condition quantifies over every error tolerance. The entire
unrestricted lower bound on this step is equivalent to existence of asymptotically
minimizing configurations carrying a single heavy isolated part. -/
theorem low_iff {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    alpha N=Jsp404.alphaN N ↔ alpha N∈scores N (lowClass k) := by
  have p:=Nat.one_le_pow k 2 (by decide)
  have ge : 3≤N := by omega
  have eq := (R52.ThreeCover.low_band lo hi).unique (R52.ThreeCover.full_staircase ge)
  have least : IsLeast (scores N (lowClass k)) (Jsp404.alphaN N) := eq ▸ low_exact lo hi
  exact ⟨fun h=>h ▸ least.1,fun h=>le_antisymm (Jsp404.alpha_le_alphaN N ge) (least.2 h)⟩

theorem high_iff {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    alpha N=Jsp404.alphaN N ↔ alpha N∈scores N (highClass k) := by
  have p:=Nat.one_le_pow k 2 (by decide)
  have ge : 3≤N := by omega
  have eq := (R52.ThreeCover.high_band lo hi).unique (R52.ThreeCover.full_staircase ge)
  have least : IsLeast (scores N (highClass k)) (Jsp404.alphaN N) := eq ▸ high_exact lo hi
  exact ⟨fun h=>h ▸ least.1,fun h=>le_antisymm (Jsp404.alpha_le_alphaN N ge) (least.2 h)⟩

end R53.Mass
#print axioms R53.Mass.low_exact
#print axioms R53.Mass.high_exact
#print axioms R53.Mass.low_iff
#print axioms R53.Mass.high_iff
