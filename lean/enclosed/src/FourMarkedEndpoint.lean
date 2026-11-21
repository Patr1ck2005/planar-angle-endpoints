import FivePatterns
noncomputable section
namespace R66.Five
open Real JSP404 R54.Profile R55.WeightedCollision Finset

/-- Four marked centers and a single label on the remaining center. -/
def lowMarks (x : Fin 5) (k : ℕ) (i : Fin 5) : ℕ :=
  if i=x then 1 else 2^k

/-- The heavy mark is indexed in the complement of the single-label center. -/
def highMarks (x : Fin 5) (p : Fin 4) (k : ℕ) (i : Fin 5) : ℕ :=
  if i=x.succAbove p then 2^(k+1) else lowMarks x k i

theorem lowMarks_pos (x : Fin 5) (k : ℕ) (i : Fin 5) : 0<lowMarks x k i := by
  unfold lowMarks;split <;> positivity

theorem highMarks_pos (x : Fin 5) (p : Fin 4) (k : ℕ) (i : Fin 5) : 0<highMarks x p k i := by
  unfold highMarks;split
  · positivity
  · exact lowMarks_pos _ _ _

theorem lowMarks_sum (x : Fin 5) (k : ℕ) : (∑i,lowMarks x k i)=4*2^k+1 := by
  rw [Fin.sum_univ_succAbove _ x]
  simp [lowMarks,Fin.succAbove_ne,Nat.add_comm]

theorem highMarks_sum (x : Fin 5) (p : Fin 4) (k : ℕ) : (∑i,highMarks x p k i)=5*2^k+1 := by
  rw [Fin.sum_univ_succAbove _ x,Fin.sum_univ_succAbove _ p]
  simp [highMarks,lowMarks,Fin.succAbove_ne,(Fin.succAbove_ne x p).symm,pow_succ]
  omega

variable {c : Fin 5→Point} {w : Fin 5→ℕ} {θ : ℝ}

/-- Exact low-band witness, on the original five distinct points at the original threshold. -/
theorem low_marked (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 4*2^k<∑i,w i) (hi : (∑i,w i)≤5*2^k) (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃x : Fin 5,θ∈attainable (lowMarks x k) c ∧ Admissible (lowMarks x k) c θ := by
  obtain ⟨x,_,ke⟩:=low_pattern ci wp hit lo hi bad
  have room (i : Fin 5) : lowMarks x k i≤2^(dim w i) := by
    by_cases eq : i=x
    · simp [lowMarks,eq]
      exact Nat.two_pow_pos _
    · obtain ⟨j,rfl⟩:=Fin.exists_succAbove_eq eq
      simp [lowMarks,Fin.succAbove_ne,ke]
  have newProfile:=replace_weights wp (lowMarks_pos x k) (fun i=>exists_ne i) ci room hit
  exact ⟨x,newProfile,(fixed_profile (lowMarks_pos x k) (fun i=>exists_ne i) ci).mp newProfile⟩

/-- Exact high-band witness, including the distinguished heavy mark. -/
theorem high_marked (ci : Function.Injective c) (wp : ∀i,0<w i) (hit : θ∈attainable w c)
    {k : ℕ} (lo : 5*2^k<∑i,w i) (hi : (∑i,w i)≤8*2^k) (bad : θ<Jsp404.alphaN (∑i,w i)) :
    ∃x : Fin 5,∃p : Fin 4,θ∈attainable (highMarks x p k) c ∧ Admissible (highMarks x p k) c θ := by
  obtain ⟨x,_,p,heavy,other⟩:=high_pattern ci wp hit lo hi bad
  have room (i : Fin 5) : highMarks x p k i≤2^(dim w i) := by
    by_cases eq : i=x
    · simp [highMarks,lowMarks,eq,(Fin.succAbove_ne x p).symm]
      exact Nat.two_pow_pos _
    · obtain ⟨j,rfl⟩:=Fin.exists_succAbove_eq eq
      by_cases jp : j=p
      · simp [highMarks,jp,heavy]
      · simp [highMarks,lowMarks,jp,Fin.succAbove_ne,other j jp]
  have newProfile:=replace_weights wp (highMarks_pos x p k) (fun i=>exists_ne i) ci room hit
  exact ⟨x,p,newProfile,(fixed_profile (highMarks_pos x p k) (fun i=>exists_ne i) ci).mp newProfile⟩

/-- At fixed physical centers, all totals and positive weights reduce exactly to these two
families of four marked centers. Each bound on the right is only for its own minimal total. -/
theorem all_weights_iff_marked (ci : Function.Injective c) :
    (∀ (v : Fin 5→ℕ), (∀i,0<v i) → ∀ t∈attainable v c,Jsp404.alphaN (∑i,v i)≤t) ↔
    ((∀ k x t, Admissible (lowMarks x k) c t → π-2*π/(2*(k:ℝ)+5)≤t) ∧
     (∀ k x p t, Admissible (highMarks x p k) c t → π-π/((k:ℝ)+3)≤t)) := by
  constructor
  · intro all
    constructor
    · intro k x t h
      have a:=all _ (lowMarks_pos x k) t (admissible_mem (lowMarks_pos x k) ci h)
      rw [lowMarks_sum] at a
      have pos:=Nat.two_pow_pos k
      have eq:=(R52.ThreeCover.full_staircase (N:=4*2^k+1) (by omega)).unique
        (R52.ThreeCover.low_band (k:=k) (by omega) (by omega))
      rwa [eq] at a
    · intro k x p t h
      have a:=all _ (highMarks_pos x p k) t (admissible_mem (highMarks_pos x p k) ci h)
      rw [highMarks_sum] at a
      have pos:=Nat.two_pow_pos k
      have eq:=(R52.ThreeCover.full_staircase (N:=5*2^k+1) (by omega)).unique
        (R52.ThreeCover.high_band (k:=k) (by omega) (by omega))
      rwa [eq] at a
  · rintro ⟨low,high⟩ v vp t hit
    let N:=∑i,v i
    have five : 5≤N := by
      calc 5=∑_ : Fin 5,1 := by simp
           _ ≤ N := sum_le_sum (fun i _=>vp i)
    let k:=Nat.clog 2 N-3
    have log : 3≤Nat.clog 2 N := (by decide : 3≤Nat.clog 2 5).trans (Nat.clog_mono_right 2 five)
    have exp : k+3=Nat.clog 2 N := by dsimp [k];omega
    have lo : 4*2^k<N := by
      have h : 2^(k+2)<N:=Nat.pow_lt_of_lt_clog (by omega)
      simpa [pow_add,Nat.mul_comm] using h
    have hi : N≤8*2^k := by
      have h:=Nat.le_pow_clog (by decide : 1<2) N
      rw [←exp,pow_add] at h
      simpa [Nat.mul_comm] using h
    change Jsp404.alphaN N≤t
    by_contra! bad
    have law:=R52.ThreeCover.full_staircase (N:=N) (by omega)
    by_cases cut : N≤5*2^k
    · obtain ⟨x,_,adm⟩:=low_marked ci vp hit lo cut bad
      rw [law.unique (R52.ThreeCover.low_band lo cut)] at bad
      exact bad.not_ge (low k x t adm)
    · have start : 5*2^k<N:=lt_of_not_ge cut
      obtain ⟨x,p,_,adm⟩:=high_marked ci vp hit start hi bad
      rw [law.unique (R52.ThreeCover.high_band start hi)] at bad
      exact bad.not_ge (high k x p t adm)

#print axioms lowMarks_sum
#print axioms highMarks_sum
#print axioms low_marked
#print axioms high_marked
#print axioms all_weights_iff_marked
end R66.Five
