import SixShapes
noncomputable section
namespace R80.Six
open Real JSP404 R54.Profile R55.WeightedCollision Finset

def mark (x : Fin 6) (d : Fin 6→ℕ) (i : Fin 6) : ℕ := if i=x then 1 else 2^d i

theorem mark_pos (x : Fin 6) (d : Fin 6→ℕ) (i : Fin 6) : 0<mark x d i := by
  unfold mark; split <;> positivity

theorem mark_sum (x : Fin 6) (d : Fin 6→ℕ) : (∑i,mark x d i)=fiveMass d x+1 := by
  rw [Fin.sum_univ_succAbove _ x]
  simp [mark,Fin.succAbove_ne,fiveMass,Nat.add_comm]

def Tests (c : Fin 6→Point) : Prop :=
  (∀ k x d, HalfPair k (fun j=>d (Fin.succAbove x j))→fiveMass d x=4*2^k→
    ∀ t∈attainable (mark x d) c, π-2*π/(2*(k:ℝ)+5)≤t) ∧
  (∀ k x d, HighFive k (fun j=>d (Fin.succAbove x j))→fiveMass d x=5*2^k→
    ∀ t∈attainable (mark x d) c, π-π/((k:ℝ)+3)≤t)

theorem all_weights_iff_three_tests {c : Fin 6→Point} (ci : Function.Injective c) :
    (∀ (v : Fin 6→ℕ), (∀i,0<v i) → ∀t∈attainable v c,Jsp404.alphaN (∑i,v i)≤t) ↔ Tests c := by
  constructor
  · intro all
    constructor
    · intro k x d _ mass t hit
      have a:=all _ (mark_pos x d) t hit
      rw [mark_sum,mass] at a
      have pos:=Nat.two_pow_pos k
      have eq:=(R52.ThreeCover.full_staircase (N:=4*2^k+1) (by omega)).unique
        (R52.ThreeCover.low_band (k:=k) (by omega) (by omega))
      rwa [eq] at a
    · intro k x d _ mass t hit
      have a:=all _ (mark_pos x d) t hit
      rw [mark_sum,mass] at a
      have pos:=Nat.two_pow_pos k
      have eq:=(R52.ThreeCover.full_staircase (N:=5*2^k+1) (by omega)).unique
        (R52.ThreeCover.high_band (k:=k) (by omega) (by omega))
      rwa [eq] at a
  · rintro ⟨low,high⟩ v vp t hit
    let N:=∑i,v i
    have six : 6≤N := by
      calc 6=∑_ : Fin 6,1 := by simp
           _ ≤ N := sum_le_sum (fun i _=>vp i)
    let k:=Nat.clog 2 N-3
    have log : 3≤Nat.clog 2 N := (by decide : 3≤Nat.clog 2 6).trans (Nat.clog_mono_right 2 six)
    have exp : k+3=Nat.clog 2 N := by dsimp [k];omega
    have lo : 4*2^k<N := by
      have h : 2^(k+2)<N:=Nat.pow_lt_of_lt_clog (by omega)
      simpa [pow_add,Nat.mul_comm] using h
    have hi : N≤8*2^k := by
      have h:=Nat.le_pow_clog (by decide : 1<2) N
      rw [←exp,pow_add] at h
      simpa [Nat.mul_comm] using h
    have mh (x : Fin 6) : t∈attainable (mark x (dim v)) c := by
      apply replace_weights vp (mark_pos _ _) (fun i=>exists_ne i) ci _ hit
      intro i
      unfold mark
      split
      · exact Nat.two_pow_pos _
      · exact le_rfl
    change Jsp404.alphaN N≤t
    by_contra! bad
    have law:=R52.ThreeCover.full_staircase (N:=N) (by omega)
    by_cases cut : N≤5*2^k
    · obtain ⟨x,mn,shape⟩:=low_shapes ci vp hit lo cut bad
      have mass:=(low_endpoint ci vp hit lo cut bad x mn).1
      rw [law.unique (R52.ThreeCover.low_band lo cut)] at bad
      exact bad.not_ge (low k x _ shape mass t (mh x))
    · have start : 5*2^k<N:=lt_of_not_ge cut
      obtain ⟨x,mn,_,shape⟩:=high_shapes ci vp hit start hi bad
      have mass:=(high_endpoint ci vp hit start hi bad x mn).1
      rw [law.unique (R52.ThreeCover.high_band start hi)] at bad
      exact bad.not_ge (high k x _ shape mass t (mh x))
end R80.Six
#print axioms R80.Six.all_weights_iff_three_tests
