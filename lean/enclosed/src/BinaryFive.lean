import SixBoundary
noncomputable section
open scoped Classical
namespace R80.Six
open Finset

/-- Exactly two of the exponents are one below k; all the others are k. -/
def HalfPair {m : ℕ} (k : ℕ) (d : Fin m→ℕ) : Prop :=
  0<k ∧ (univ.filter (fun i=>d i<k)).card=2 ∧ ∀i,d i=k ∨ d i+1=k

theorem one_unit_missing {m k : ℕ} {d : Fin (m+1)→ℕ} (caps : ∀i,d i≤k)
    (mass : (∑i,2^d i)=m*2^k) : HalfPair k d := by
  classical
  cases k with
  | zero =>
    have eq : d=fun _=>0:=funext (fun i=>Nat.eq_zero_of_le_zero (caps i))
    simp [eq] at mass
  | succ t =>
    let L:=univ.filter (fun i=>d i<t+1)
    let U:=univ.filter (fun i=>¬d i<t+1)
    let v:=2^t
    have vp:0<v:=Nat.two_pow_pos _
    have cap (i) (hi:i∈L):2^d i≤v:=
      Nat.pow_le_pow_right (by decide) (by have :=(mem_filter.mp hi).2;omega)
    have big (i) (hi:i∈U):2^d i=2*v := by
      have eq:d i=t+1:=by have :=(mem_filter.mp hi).2;have :=caps i;omega
      simp [eq,v,pow_succ,Nat.mul_comm]
    have lg:(∑i∈U,2^d i)=U.card*(2*v):=by
      calc _=∑_i∈U,2*v:=sum_congr rfl big
           _=_:=by simp
    have counts:L.card+U.card=m+1:=by
      simpa [L,U] using card_filter_add_card_filter_not (s:=(univ : Finset (Fin (m+1)))) (fun i=>d i<t+1)
    have both:(∑i∈L,2^d i)+(∑i∈U,2^d i)=∑i,2^d i:=sum_filter_add_sum_filter_not .. 
    rw [lg,mass,pow_succ] at both
    change (∑i∈L,2^d i)+U.card*(2*v)=m*(v*2) at both
    have mu:=congrArg (fun z : ℕ=>z*(2*v)) counts
    change (L.card+U.card)*(2*v)=(m+1)*(2*v) at mu
    have balance : (∑i∈L,2^d i)+2*v=L.card*(2*v):=by nlinarith only [both,mu]
    have lower : L.card≤∑i∈L,2^d i:=by
      simpa using sum_le_sum (s:=L) (fun i _=>show 1≤2^d i from Nat.one_le_two_pow)
    have upper : (∑i∈L,2^d i)≤L.card*v:=by simpa using sum_le_sum (s:=L) cap
    have size : L.card=2:=by
      by_cases hi : 3≤L.card
      · have h:=Nat.mul_le_mul_right v hi
        nlinarith only [balance,upper,h,vp]
      · by_contra ne
        rcases (show L.card=0 ∨ L.card=1 by omega) with z|one
        · rw [z,zero_mul] at balance;omega
        · rw [one,one_mul] at balance;omega
    refine ⟨by omega,size,?_⟩
    intro i
    by_cases h:d i=t+1
    · exact Or.inl h
    · right
      have di:=caps i
      have elem : i∈L:=mem_filter.mpr ⟨mem_univ _,by omega⟩
      by_contra! ne
      have lt : d i<t:=by omega
      have strict:=sum_lt_sum (s:=L) cap ⟨i,elem,Nat.pow_lt_pow_right (by decide : 1<2) lt⟩
      simp only [sum_const,nsmul_eq_mul,size] at strict balance
      omega

/-- Five retained sites in the upper strip either fill the same level
or have one doubled level and exactly two half levels. -/
def HighFive (k : ℕ) (d : Fin 5→ℕ) : Prop :=
  (∀i,d i=k) ∨ ∃p : Fin 5,d p=k+1 ∧ HalfPair k (fun j=>d (p.succAbove j))

end R80.Six
#print axioms R80.Six.one_unit_missing
