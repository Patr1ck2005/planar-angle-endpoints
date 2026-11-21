import ConcyclicStaircase
import FixedCenterGap

noncomputable section
namespace R62.Anchors
open Real JSP404 R54.GapTest R56.Windows R55.WeightedCollision

def pair (a b : Point) : Fin 2→Point:=![a,b]
def twoScores (N : ℕ) (a b : Point) : Set ℝ := {θ | ∃ w : Fin 2→ℕ,
  (∀i,0<w i) ∧ (∑i,w i)=N ∧ θ∈attainable w (pair a b)}

theorem pair_inj {a b : Point} (ab : a≠b) : Function.Injective (pair a b) := by
  intro i j e
  fin_cases i <;> fin_cases j <;> simp_all [pair]

private def oneRow (t : ℝ) : Row 1 where
  w j := t+(j:ℝ)*π
  ordered := by intro a b h _;gcongr
  period := by norm_num

theorem fixed_pair {a b : Point} (ab : a≠b) {w : Fin 2→ℕ} (wp : ∀i,0<w i) {l : ℝ} (lp : 0<l) :
    π-l∈attainable w (pair a b) ↔ 0≤π-l ∧ ∀i,w i≤2^(⌊π/l⌋₊-1) := by
  let c:=pair a b
  let ci:=pair_inj ab
  let n (i : Fin 2) : Fin 2:=if i=0 then 1 else 0
  have ne (i) : i≠n i := by fin_cases i <;> decide
  have only (i j) (ij : i≠j) : j=n i := by fin_cases i <;> fin_cases j <;> simp_all [n]
  choose t _ _ line using fun i=>polar (c (n i)-c i) (sub_ne_zero.mpr (ci.ne (ne i).symm))
  let R (i : Fin 2):=oneRow (t i)
  have rep : Represents R c := by
    intro i j ij
    rw [only i j ij]
    refine ⟨0,Nat.zero_le _,?_⟩
    change Bearing (c (n i)-c i) ((R i).w 0)
    simpa [R,oneRow] using line i
  have wit : Witnessed R c := by
    intro i k hk
    change k≤1 at hk
    refine ⟨n i,ne i,?_⟩
    interval_cases k
    · simpa [R,oneRow] using line i
    · simpa [R,oneRow] using bearing_closes (line i)
  have empty : Macro c (π-l) := by
    intro i j k ij ik jk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> contradiction
  have scr (i) : score R i l=⌊π/l⌋₊-1 := by simp [score,R,oneRow,R51.Anchored.gapScore]
  rw [fixed_centers_iff R ci rep wit wp,or_iff_right (show ¬π≤π-l by linarith),sub_sub_cancel,
    and_iff_right empty]
  simp_rw [scr,Nat.clog_le_iff_le_pow (by decide : 1<2)]

theorem two_at {a b : Point} (ab : a≠b) {N : ℕ} (ge : 2≤N) {l : ℝ} (lp : 0<l) :
    π-l∈twoScores N a b ↔ 0≤π-l ∧ N≤2*2^(⌊π/l⌋₊-1) := by
  constructor
  · rintro ⟨w,wp,sz,hit⟩
    obtain ⟨pos,cap⟩:=(fixed_pair ab wp lp).mp hit
    rw [Fin.sum_univ_two] at sz
    exact ⟨pos,by linarith [cap 0,cap 1]⟩
  · rintro ⟨pos,count⟩
    let w : Fin 2→ℕ:=![N/2,N-N/2]
    have wp (i) : 0<w i := by fin_cases i <;> simp [w] <;> omega
    refine ⟨w,wp,by simp [Fin.sum_univ_two,w];omega,(fixed_pair ab wp lp).mpr ⟨pos,?_⟩⟩
    intro i;fin_cases i <;> simp [w] <;> omega

def dyadic (N : ℕ) := π-π/(Nat.clog 2 N:ℝ)

theorem two_increasing {a b : Point} {N : ℕ} {θ η : ℝ} (hit : θ∈twoScores N a b) (le : θ≤η) :
    η∈twoScores N a b := by
  obtain ⟨w,wp,sz,h⟩:=hit
  refine ⟨w,wp,sz,?_⟩
  intro e ep;obtain ⟨f,inj,rad,cap⟩:=h e ep
  exact ⟨f,inj,rad,by linarith⟩

theorem two_spectrum {N : ℕ} (ge : 3≤N) {a b : Point} (ab : a≠b) : twoScores N a b=Set.Ici (dyadic N) := by
  let d:=Nat.clog 2 N
  have dp : 0<d := Nat.clog_pos (by decide) (by omega)
  have dr : (0:ℝ)<d := by exact_mod_cast dp
  have one : (1:ℝ)≤d := by exact_mod_cast dp
  have base : dyadic N∈twoScores N a b := by
    change π-π/(d:ℝ)∈_
    apply (two_at ab (by omega) (div_pos pi_pos dr)).mpr
    refine ⟨sub_nonneg.mpr ((div_le_iff₀ dr).mpr (by nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr one)])),?_⟩
    rw [show π/(π/(d:ℝ))=(d:ℝ) by field_simp,Nat.floor_natCast,←Nat.pow_succ',
      show (d-1).succ=d by omega]
    exact Nat.le_pow_clog (by decide) N
  ext θ
  refine ⟨?_,fun h=>two_increasing base h⟩
  intro hit
  change π-π/(d:ℝ)≤θ
  by_cases high : π≤θ
  · linarith [div_pos pi_pos dr]
  let l:=π-θ
  have lp : 0<l := by dsimp [l];linarith
  have e : π-l=θ := by dsimp [l];ring
  obtain ⟨pos,ub⟩:=(two_at ab (by omega) lp).mp (show π-l∈twoScores N a b by rwa [e])
  have floor_pos : 1≤⌊π/l⌋₊ := (Nat.le_floor_iff (div_nonneg pi_pos.le lp.le)).mpr (by
    rw [le_div_iff₀ lp]; push_cast;linarith)
  rw [←Nat.pow_succ',show (⌊π/l⌋₊-1).succ=⌊π/l⌋₊ by omega] at ub
  have dlow : d≤⌊π/l⌋₊ := Nat.clog_le_of_le_pow ub
  have rr:=(Nat.le_floor_iff (div_nonneg pi_pos.le lp.le)).mp dlow
  have pd:= (le_div_iff₀ lp).mp rr
  have low : l≤π/(d:ℝ) := (le_div_iff₀ dr).mpr (by nlinarith)
  dsimp [l] at low;linarith

#print axioms fixed_pair
#print axioms two_spectrum
end R62.Anchors

