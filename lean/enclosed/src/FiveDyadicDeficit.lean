import ApexCone
noncomputable section
namespace R70.IntegerApex
open Real Finset JSP404 R55.WeightedCollision R54.GapTest R54.Profile

/-- Distinct triples of narrow centers would give a triangle of total angle less than pi. -/
theorem at_most_two {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w:I→ℕ} {l : ℝ} (lp:0<l) {k:ℕ} (kp:2≤k)
    (per : (k+2:ℕ)*l=π) (many : ∀i:I,3≤Fintype.card (Peer i))
    (A : Admissible w c (π-l)) : (univ.filter (fun i=>k≤dim w i)).card≤2 := by
  classical
  by_contra! bad
  obtain ⟨a,ha,b,hb,d,hd,ab,ad,bd⟩:=two_lt_card.mp bad
  have narrow:=apexes ci lp (by omega : 0<k) per many A
  have ba:=(narrow a).2 (mem_filter.mp ha).2 ⟨d,ad⟩ ⟨b,ab⟩
  have bb:=(narrow b).2 (mem_filter.mp hb).2 ⟨a,ab.symm⟩ ⟨d,bd⟩
  have bd':=(narrow d).2 (mem_filter.mp hd).2 ⟨b,bd.symm⟩ ⟨a,ad.symm⟩
  have sum:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c d) (ci.ne ab.symm)
  change EuclideanGeometry.angle (c a) (c b) (c d)+EuclideanGeometry.angle (c b) (c d) (c a)+EuclideanGeometry.angle (c d) (c a) (c b)=π at sum
  dsimp only at ba bb bd'
  have eq : ((k:ℝ)+2)*l=π := by simpa using per
  have h:(2:ℝ)≤k:=by exact_mod_cast kp
  nlinarith only [sum,ba,bb,bd',eq,lp,mul_le_mul_of_nonneg_right h lp.le]

/-- At an integer parameter d+3 at least four sites have aggregate rounded mass at most
(cardinality + 2) times 2^d. -/
theorem rounded_mass {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w:I→ℕ} {l : ℝ} (lp:0<l) {d:ℕ} (dp:0<d)
    (per : (d+3:ℕ)*l=π) (many : ∀i:I,3≤Fintype.card (Peer i))
    (A : Admissible w c (π-l)) : (∑i,2^dim w i)≤(Fintype.card I+2)*2^d := by
  classical
  let H:=univ.filter (fun i=>d+1≤dim w i)
  have size : H.card≤2:=at_most_two ci lp (by omega : 2≤d+1) per many A
  have ub:=apexes ci lp (by omega : 0<d+1) per many A
  have each (i:I) : 2^dim w i≤2^d+(if i∈H then 2^d else 0) := by
    by_cases h:i∈H
    · have a:=Nat.pow_le_pow_right (by decide : 0<2) (ub i).1
      rw [pow_succ] at a
      simpa [h,Nat.mul_two] using a
    · have b : dim w i≤d := by simp [H] at h;omega
      simpa [h] using Nat.pow_le_pow_right (by decide : 0<2) b
  calc
    _≤∑i,(2^d+(if i∈H then 2^d else 0)) := sum_le_sum (fun i _=>each i)
    _=Fintype.card I*2^d+H.card*2^d := by simp [sum_add_distrib]
    _≤_ := by rw [Nat.add_mul];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ size) _

/-- Every attainable fixed five-site family has at least one eighth of its dyadic mass missing. -/
theorem five_fixed {d:ℕ} (dp:0<d) (c:Fin 5→Point) (ci:Function.Injective c)
    (w:Fin 5→ℕ) (wp:∀i,0<w i)
    (hit : π-π/(d+3:ℕ)∈attainable w c) : (∑i,w i)≤7*2^d := by
  have len : (0:ℝ)<(d+3:ℕ) := by positivity
  have actual:=(fixed_profile wp (fun _=>exists_ne _) ci).mp hit
  have other (i:Fin 5):3≤Fintype.card (Peer i) := by
    fin_cases i <;> decide
  have cap:=rounded_mass ci (div_pos pi_pos len) dp (by field_simp) other actual
  exact (sum_le_sum (fun i _=>Nat.le_pow_clog (by decide : 1<2) (w i))).trans (by simpa using cap)
end R70.IntegerApex
#print axioms R70.IntegerApex.at_most_two
#print axioms R70.IntegerApex.rounded_mass
#print axioms R70.IntegerApex.five_fixed
