import ThreeCoverLower
import TwoToThree
import SendovScores
import Jsp000404.UpperBound

noncomputable section
namespace R52.ThreeCover
open JSP404 Real R51.TwoCenters

theorem low_band {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    IsLeast (scores N) (π-2*π/(2*(k:ℝ)+5)) := by
  have p:=Nat.one_le_pow k 2 (by decide)
  exact ⟨R52.SendovCloud.mem_scores (by omega) hi,fun _ hu=>low_bound lo hu⟩

theorem high_band {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    IsLeast (scores N) (π-π/((k:ℝ)+3)) := by
  have p:=Nat.one_le_pow k 2 (by decide)
  exact ⟨high_approach (by omega) hi,fun _ hu=>high_bound lo hu⟩

theorem large_staircase {N : ℕ} (five : 5≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  let k:=Nat.clog 2 N-3
  let n:=Nat.clog 2 N-1
  have log : 3≤Nat.clog 2 N := by
    have h:=Nat.clog_mono_right 2 five
    exact le_trans (by decide : 3≤Nat.clog 2 5) h
  have nk : n=k+2 := by dsimp [n,k];omega
  have exp : k+3=Nat.clog 2 N := by dsimp [k];omega
  have low : 4*2^k<N := by
    have h : 2^(k+2)<N := Nat.pow_lt_of_lt_clog (by omega)
    simpa [pow_add,Nat.mul_comm] using h
  have high : N≤8*2^k := by
    have h:=Nat.le_pow_clog (by decide : 1<2) N
    rw [←exp,pow_add] at h
    simpa [Nat.mul_comm] using h
  rw [Jsp404.alphaN_of_ge_four (by omega) (n:=n) rfl]
  have zp : (2:ℝ)^((n:ℤ)-2)=(2:ℝ)^k := by
    have eq : (n:ℤ)-2=(k:ℤ) := by rw [nk];push_cast;ring
    rw [eq,zpow_natCast]
  rw [zp,nk,pow_add]
  have cut : ((N:ℝ)≤2^k*2^2+2^k) ↔ N≤5*2^k := by
    rw [show (2:ℝ)^k*2^2+2^k=5*2^k by ring]
    exact_mod_cast Iff.rfl
  by_cases le : N≤5*2^k
  · rw [if_pos (cut.mpr le)]
    convert low_band low le using 1
    push_cast;ring
  · rw [if_neg (fun h=>le (cut.mp h))]
    convert high_band (lt_of_not_ge le) high using 1
    push_cast;ring


end R52.ThreeCover
#print axioms R52.ThreeCover.large_staircase
