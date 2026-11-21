import FiveStaircaseConsequences
import FiveFamily
noncomputable section
namespace R67.FiveCapacity
open JSP404 Real R55.WeightedCollision R54.GapTest R64.Five
/-- Total weights realized at exactly five distinct (freely chosen) macrocenters. -/
def totals (θ : ℝ) : Set ℕ := {N | ∃c : Fin 5→Point,Function.Injective c ∧
  ∃w : Fin 5→ℕ,(∀i,0<w i) ∧ (∑i,w i)=N ∧ θ∈attainable w c}

private theorem all_smaller {w : Fin 5→ℕ} {c : Fin 5→Point} (ci : Function.Injective c)
    (wp : ∀i,0<w i) {θ : ℝ} (lt : θ<π) (hit : θ∈attainable w c) {M : ℕ}
    (lo : 5≤M) (hi : M≤∑i,w i) : ∃v : Fin 5→ℕ,(∀i,0<v i) ∧ (∑i,v i)=M ∧ θ∈attainable v c := by
  obtain ⟨m,R,front,back⟩:=R54.GapTest.actual_rows c ci
  have A:=(R54.Profile.fixed_profile wp (fun i=>exists_ne i) ci).mp hit
  have all:=R65.Retention.positive_mass_iff ci R front back A.1 lt A.2.1
  have room:=(all (∑i,w i)).mp ⟨w,wp,rfl,hit⟩
  exact (all M).mpr ⟨by simpa using lo,hi.trans room.2⟩

theorem upper_of_law (law : R67.Board.FiniteBoardLaw) (k : ℕ) {θ : ℝ}
    (below : θ<π-π/((k:ℝ)+3)) {N : ℕ} (hit : N∈totals θ) : N≤5*2^k := by
  obtain ⟨c,ci,w,wp,sz,att⟩:=hit
  by_contra! ex
  have d : 0<(k:ℝ)+3 := by positivity
  have lt : θ<π:=by linarith [div_pos pi_pos d]
  let B:=5*2^k
  have pp:=Nat.two_pow_pos k
  obtain ⟨v,vp,size,ok⟩:=all_smaller ci wp lt att (M:=B+1) (by dsimp [B];omega) (by rw [sz];exact ex)
  have lower:=R67.Board.five_of_finite law ci v vp ok
  rw [size] at lower
  have hi : B+1≤8*2^k := by dsimp [B];omega
  have eq:=(R52.ThreeCover.full_staircase (N:=B+1) (by dsimp [B];omega)).unique
    (R52.ThreeCover.high_band (show 5*2^k<B+1 from Nat.lt_succ_self _) hi)
  linarith [eq]

/-- On the upper quarter of every sufficiently large strip, the maximum
over exactly five centers is attained on the explicit R64 nonconcyclic
five-site family. All smaller admissible cardinalities occur there as well. -/
theorem interval_of_law (law : R67.Board.FiniteBoardLaw) {n : ℕ} (hn : 16≤n) {θ : ℝ}
    (lower : π-defect n≤θ) (upper : θ<π-π/((n:ℝ)+1)) :
    totals θ=Set.Icc 5 (size n) := by
  have ne : 2≤n:=by omega
  have eq : ((n-2:ℕ):ℝ)+3=(n:ℝ)+1 := by rw [Nat.cast_sub ne];push_cast;ring
  have lt : θ<π:=by linarith [div_pos pi_pos (show 0<(n:ℝ)+1 by positivity)]
  ext N
  constructor
  · intro mem
    have actual:=mem
    obtain ⟨c,ci,w,wp,sz,_⟩:=actual
    have count:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>show 1≤w i from wp i)
    refine ⟨by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,sz] using count,?_⟩
    exact upper_of_law law (n-2) (by rwa [eq]) mem
  · intro bounds
    have att : θ∈attainable (weight n) (point (defect n)) := by
      intro ε hp
      obtain ⟨f,fi,dist,score⟩:=five_attainable hn ε hp
      exact ⟨f,fi,dist,by linarith⟩
    have fits : N≤∑i,weight n i := by rw [mass];exact bounds.2
    obtain ⟨w,wp,sz,ok⟩:=all_smaller (injective _) (fun _=>Nat.two_pow_pos _) lt att bounds.1 fits
    exact ⟨_,injective _,w,wp,sz,ok⟩
#print axioms upper_of_law
#print axioms interval_of_law
end R67.FiveCapacity
