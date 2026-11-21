import AngularBlockers
import FixedPair
import CommonDirections

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention

theorem kit_cap {m B d : ℕ} (three : 3≤m) {c : Fin m→Point} (ci : Function.Injective c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) (crit : Critical c (B+1) θ)
    (u : Fin d→Point) (kit : InternalTrial u θ) : 2^d≤B := by
  let l:=π-θ
  have lp : 0<l := sub_pos.mpr below
  have lp' : π-l=θ := sub_sub_cancel _ _
  let e : Fin 2↪Fin m := Fin.castLEEmb (by omega)
  let c' := c ∘ e
  have ci' : Function.Injective c' := ci.comp e.injective
  have pair : R62.Anchors.pair (c' 0) (c' 1)=c' := by funext k;fin_cases k <;> rfl
  let F:=⌊π/l⌋₊
  let w (_ : Fin 2) := (2:ℕ)^(F-1)
  have wp (i : Fin 2) : 0<w i := pow_pos (by decide) _
  have hit:= (R62.Anchors.fixed_pair (ci'.ne (by decide : (0:Fin 2)≠1)) wp lp).mpr
    ⟨lp'.symm ▸ pos,fun _=>le_rfl⟩
  rw [pair,lp'] at hit
  have legal : Macro c' θ := by
    intro i j k ij ik jk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> contradiction
  obtain ⟨p,Q,front,back⟩:=actual_rows c' ci'
  have fit:= (fits_iff ci' Q front back pos below legal wp).mp hit
  have sum:=sum_le_sum (s:=univ) (fun i _=>fit i)
  have tight : capacity Q θ≤B := Nat.le_of_lt_succ (crit (by decide) (by omega) e Q front back)
  change (∑i : Fin 2,w i)≤capacity Q θ at sum
  have bound : 2*2^(F-1)≤B := by simpa [w,Fin.sum_univ_two,two_mul] using sum.trans tight
  have dF : d≤F := by
    simpa [F] using R66.Common.signed_budget u kit.1 lp (by dsimp [l];linarith) (by simpa only [lp'] using kit.2)
  calc _ ≤ 2^((F-1)+1) := Nat.pow_le_pow_right (by decide) (by omega)
       _ = 2*2^(F-1) := pow_succ' _ _
       _ ≤ B := bound

/-- Every proposed positive increase intersects a quantified mass of other
real sites, including when the apex is the only site compatible with the kit.
There is no assumption on the number or location of its obstructing neighbors. -/
theorem all_blockers {m B v : ℕ} (three : 3≤m) {c : Fin m→Point} (ci : Function.Injective c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) {s : Fin m→ℕ} (R : ∀i,Row (s i))
    (front : Represents R c) (back : Witnessed R c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) (j : Fin m) {r : ℕ} (rp : 0<r)
    (u : Fin (score R j (π-θ)+r)→Point) (kit : InternalTrial u θ) :
    v+(2^r-1)*mass R θ j≤∑i∈blockers c θ j u,mass R θ i := by
  classical
  let D:=blockers c θ j u
  by_cases many : 2≤(univ \ D).card
  · exact blocker_mass R ci full crit below front back j rp u kit many
  have dj : j∉D := by simp [D,blockers]
  have only : ∀i,i∉D → i=j := by
    intro i hi
    exact card_le_one.mp (show (univ \ D).card≤1 by omega)
      i (mem_sdiff.mpr ⟨mem_univ _,hi⟩) j (mem_sdiff.mpr ⟨mem_univ _,dj⟩)
  have eq : D=univ.erase j := by
    ext i;simp only [mem_erase,mem_univ,and_true]
    exact ⟨fun h same=>dj (same ▸ h),fun ne=>by_contra (fun bad=>ne (only i bad))⟩
  have split:=sum_erase_add (s:=univ) (mass R θ) (mem_univ j)
  change (∑i,mass R θ i)=B+v at full
  have cap:=kit_cap three ci pos below crit u kit
  change 2^(score R j (π-θ)+r)≤B at cap
  rw [pow_add,mul_comm] at cap
  change v+(2^r-1)*mass R θ j≤∑i∈D,mass R θ i
  rw [eq,Nat.sub_mul,one_mul]
  have mk : mass R θ j≤2^r*mass R θ j := Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  change 2^r*mass R θ j≤B at cap
  omega

end R85.CriticalMass
#print axioms R85.CriticalMass.kit_cap
#print axioms R85.CriticalMass.all_blockers
