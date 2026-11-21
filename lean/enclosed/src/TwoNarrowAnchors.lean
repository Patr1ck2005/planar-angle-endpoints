import AnchorFrame
import JSP404.Basic
import Mathlib.Data.Nat.Log

noncomputable section
namespace R53.TwoAnchor
open Real JSP404 TwoAnchorGeometry TwoAnchorCount InnerProductGeometry

/-- Every distinct pair of other points subtends an angle strictly below λ at a. -/
def Narrow (S : Finset Point) (a : Point) (lam : ℝ) : Prop :=
  ∀ x∈S, ∀ y∈S, x≠a → y≠a → x≠y → EuclideanGeometry.angle x a y<lam

/-- Ordinary two-anchor count for an arbitrary finite set of actual plane points. -/
theorem ordinary_floor {S : Finset Point} {a b : Point} {lam : ℝ}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) (hl : 0<lam) (hlπ : lam≤π/2)
    (cap : maxAngle S≤π-lam) (na : Narrow S a lam) (nb : Narrow S b lam) :
    ((S.erase a).erase b).card ≤ 2^(⌊π/lam⌋₊-2) := by
  classical
  let G := (S.erase a).erase b
  have hm (i : G) : i.val∈S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase i.property)
  have ia (i : G) : i.val≠a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase i.property)).1
  have ib (i : G) : i.val≠b := (Finset.mem_erase.mp i.property).1
  obtain ⟨Z,zinj,za,zb,zang⟩ := baseline ab
  let z (i : G) := Z i.val
  have zn (i : G) : z i≠0 := by rw [←za]; exact zinj.ne (ia i)
  have on (i : G) : z i≠1 := by rw [←zb]; exact zinj.ne (ib i)
  have angleZ (x y t : Point) :
      angle (Z x-Z y) (Z t-Z y)=EuclideanGeometry.angle x y t := zang _ _ _
  have A (i : G) : angle 1 (z i)<lam := by
    have h := na b hb _ (hm i) ab.symm (ia i) (ib i).symm
    rw [←angleZ,za,zb,sub_zero,sub_zero] at h
    exact h
  have B (i : G) : angle 1 (1-z i)<lam := by
    have h := nb a ha _ (hm i) ab (ib i) (ia i).symm
    rw [←angleZ,za,zb,zero_sub,angle_neg_left] at h
    rw [←neg_sub (Z i.val) 1,angle_neg_right]
    exact h
  have C (i : G) : angle (-(z i)) (1-z i)≤π-lam := by
    have h := (angle_le_maxAngle ha (hm i) hb (ia i).symm ab (ib i)).trans cap
    rw [←angleZ,za,zb,zero_sub] at h
    exact h
  have A' (i j : G) (ne : i≠j) : angle (z i) (z j)<lam := by
    have h := na _ (hm i) _ (hm j) (ia i) (ia j) (Subtype.val_injective.ne ne)
    rw [←angleZ,za,sub_zero,sub_zero] at h
    exact h
  have B' (i j : G) (ne : i≠j) : angle (1-z i) (1-z j)<lam := by
    have h := nb _ (hm i) _ (hm j) (ib i) (ib j) (Subtype.val_injective.ne ne)
    rw [←angleZ,zb] at h
    rwa [←neg_sub (z i) 1,←neg_sub (z j) 1,angle_neg_neg]
  obtain ⟨strip,side⟩ := chart_side z hl hlπ zn on A B C A' B'
  obtain ⟨F,finj,f0,f1,fang,fx,fy⟩ := lift_side z strip side
  let E (x : Point) := F (Z x)
  have EI : Function.Injective E := finj.comp zinj
  have Ea : E a=0 := by simp [E,za,f0]
  have Eb : E b=base := by simp [E,zb,f1]
  have ang (x y t : Point) :
      angle (E x-E y) (E t-E y)=EuclideanGeometry.angle x y t := (fang _ _ _).trans (angleZ _ _ _)
  let P (i : G) := E i.val
  have lfloor : 2≤⌊π/lam⌋₊ := (Nat.le_floor_iff (div_nonneg pi_pos.le hl.le)).mpr
    ((le_div_iff₀ hl).mpr (by norm_num; linarith))
  have H := fixed_anchor_count P (EI.comp Subtype.val_injective) hl (by linarith [pi_pos]) lfloor fx fy
  have ma (i : G) : angle base (P i)<lam := by
    have h := na b hb _ (hm i) ab.symm (ia i) (ib i).symm
    simpa only [←ang,Ea,Eb,sub_zero,P] using h
  have mb (i : G) : angle (-base) (P i-base)<lam := by
    have h := nb a ha _ (hm i) ab (ib i) (ia i).symm
    simpa only [←ang,Ea,Eb,zero_sub,P] using h
  have liftPoint (y : Plane) (h : y∈({0,base} : Set Plane) ∪ Set.range P) :
      ∃ x∈S, E x=y := by
    rcases h with h | ⟨i,rfl⟩
    · rcases (show y=0 ∨ y=base by simpa using h) with rfl | rfl
      · exact ⟨a,ha,Ea⟩
      · exact ⟨b,hb,Eb⟩
    · exact ⟨i.val,hm i,rfl⟩
  have legal : Legal (({0,base} : Set Plane) ∪ Set.range P) lam := by
    intro x hx y hy t ht xy yt xt
    obtain ⟨p,hp,rfl⟩ := liftPoint x hx
    obtain ⟨q,hq,rfl⟩ := liftPoint y hy
    obtain ⟨r,hr,rfl⟩ := liftPoint t ht
    rw [ang]
    exact (angle_le_maxAngle hp hq hr (fun e=>xy (congrArg E e)) (fun e=>xt (congrArg E e))
      (fun e=>yt (congrArg E e))).trans cap
  simpa only [Fintype.card_coe] using H ma mb legal

/-- Exact closed endpoint, including a dyadic cardinality of the remainder. -/
theorem ordinary_clog {S : Finset Point} {a b : Point} {lam : ℝ}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) (hl : 0<lam) (hlπ : lam≤π/2)
    (cap : maxAngle S≤π-lam) (na : Narrow S a lam) (nb : Narrow S b lam) :
    ((Nat.clog 2 ((S.erase a).erase b).card : ℝ)+2)*lam≤π := by
  have HC := Nat.clog_le_of_le_pow (ordinary_floor ha hb ab hl hlπ cap na nb)
  have h2 : 2≤⌊π/lam⌋₊ := Nat.le_floor ((le_div_iff₀ hl).2 (by norm_num; linarith))
  have count : Nat.clog 2 ((S.erase a).erase b).card+2≤⌊π/lam⌋₊ := by omega
  have h' : (Nat.clog 2 ((S.erase a).erase b).card : ℝ)+2≤(⌊π/lam⌋₊:ℝ) := by exact_mod_cast count
  exact (le_div_iff₀ hl).mp (h'.trans (Nat.floor_le (div_nonneg pi_pos.le hl.le)))

/-- Threshold form for an arbitrary bit budget m.  The strict threshold is on π. -/
theorem ordinary_count {S : Finset Point} {a b : Point} {lam : ℝ} {m : ℕ}
    (ha : a∈S) (hb : b∈S) (ab : a≠b) (hl : 0<lam) (hlπ : lam≤π/2)
    (cap : maxAngle S≤π-lam) (na : Narrow S a lam) (nb : Narrow S b lam)
    (threshold : π<((m:ℝ)+3)*lam) : ((S.erase a).erase b).card≤2^m := by
  have h := ordinary_clog ha hb ab hl hlπ cap na nb
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp
  by_contra! no
  have one : (m:ℝ)+1≤Nat.clog 2 ((S.erase a).erase b).card := by exact_mod_cast no
  nlinarith [mul_nonneg (sub_nonneg.mpr one) hl.le]

#print axioms ordinary_floor
#print axioms ordinary_clog
#print axioms ordinary_count
end R53.TwoAnchor
