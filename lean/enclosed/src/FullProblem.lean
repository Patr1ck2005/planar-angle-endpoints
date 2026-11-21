import SevenSeparated
import CriticalEndpointProfile

noncomputable section
namespace R85.Original
open JSP404 R54.GapTest R55.WeightedCollision R56.Windows R65.Retention R85.CriticalMass

def AllCardinalities : Prop := ∀ N : ℕ, 3≤N → alpha N=Jsp404.alphaN N

/-- It suffices to prove the two leftmost cardinalities of every dyadic band. -/
theorem endpoints : AllCardinalities ↔
    ∀ b k : ℕ, (b=4 ∨ b=5) → alpha (b*2^k+1)=Jsp404.alphaN (b*2^k+1) := by
  constructor
  · intro all b k shape
    have hp:=Nat.two_pow_pos k
    apply all
    rcases shape with rfl|rfl <;> omega
  · intro all N ge
    by_cases small : N≤4
    · apply (R67.FiveCenter.unrestricted_iff_six ge).mpr
      intro size large fit; omega
    let k:=Nat.clog 2 N-3
    have log : 3≤Nat.clog 2 N :=
      (by decide : 3≤Nat.clog 2 5).trans (Nat.clog_mono_right 2 (by omega : 5≤N))
    have exp : k+3=Nat.clog 2 N := by dsimp [k]; omega
    have lo : 4*2^k<N := by
      have h : 2^(k+2)<N := Nat.pow_lt_of_lt_clog (by omega)
      simpa [pow_add,Nat.mul_comm] using h
    have hi : N≤8*2^k := by
      have h:=Nat.le_pow_clog (by decide : 1<2) N
      rw [←exp,pow_add] at h
      simpa [Nat.mul_comm] using h
    have hp:=Nat.two_pow_pos k
    apply le_antisymm (Jsp404.alpha_le_alphaN N ge)
    by_cases cut : N≤5*2^k
    · let E:=4*2^k+1
      have ee : 3≤E := by dsimp [E];omega
      have val:=(R52.ThreeCover.full_staircase ge).unique (R52.ThreeCover.low_band lo cut)
      have left:=(R52.ThreeCover.full_staircase ee).unique
        (R52.ThreeCover.low_band (k:=k) (by dsimp [E];omega) (by dsimp [E];omega))
      calc Jsp404.alphaN N = Jsp404.alphaN E := val.trans left.symm
           _ = alpha E := (all 4 k (Or.inl rfl)).symm
           _ ≤ alpha N := alpha_mono ee (by dsimp [E];omega)
    · let E:=5*2^k+1
      have ee : 3≤E := by dsimp [E];omega
      have val:=(R52.ThreeCover.full_staircase ge).unique (R52.ThreeCover.high_band (lt_of_not_ge cut) hi)
      have left:=(R52.ThreeCover.full_staircase ee).unique
        (R52.ThreeCover.high_band (k:=k) (by dsimp [E];omega) (by dsimp [E];omega))
      calc Jsp404.alphaN N = Jsp404.alphaN E := val.trans left.symm
           _ = alpha E := (all 5 k (Or.inr rfl)).symm
           _ ≤ alpha N := alpha_mono ee (by dsimp [E];omega)

def Profiles (t b k : ℕ) : Prop :=
  ∀ h : ℕ, t≤h → h+1≤b*2^k+1 → ∀ c : Fin (h+1)→Point, Function.Injective c →
  ¬ R58.CircleModel.OnCircle c → ∀ θ : ℝ, 0≤θ → θ<Real.pi → Macro c θ →
  ∀ {m : Fin (h+1)→ℕ}, ∀ R : (i : Fin (h+1))→Row (m i), Represents R c → Witnessed R c →
  Critical c (b*2^k+1) θ → ∀ x, Profile c θ R x (b*2^k) k → Jsp404.alphaN (b*2^k+1)≤θ

/-- An arbitrary number of sites and all ordinary cardinalities, in a single exact equivalence. -/
theorem full_iff_profiles : AllCardinalities ↔ ∀ b k, (b=4 ∨ b=5) → Profiles 5 b k := by
  rw [endpoints]
  exact forall_congr' (fun b=>forall_congr' (fun k=>forall_congr' (fun s=>
    unrestricted_endpoint_iff b k s)))

/-- Use of the six-site result is isolated in the sole explicit hypothesis. -/
theorem full_iff_seven (six : ∀ b k, (b=4 ∨ b=5) → R85.Seven.SixAt (b*2^k+1)) :
    AllCardinalities ↔ ∀ b k, (b=4 ∨ b=5) → Profiles 6 b k := by
  rw [full_iff_profiles]
  constructor
  · intro ok b k shape h lb
    exact ok b k shape h (by omega)
  · intro ok b k shape h lb small c ci nc θ pos below mac m R front back critical x P
    by_cases large : 6≤h
    · exact ok b k shape h large small c ci nc θ pos below mac R front back critical x P
    obtain rfl : h=5 := by omega
    obtain ⟨w,wp,sz,hit⟩:=(positive_mass_iff ci R front back pos below mac (b*2^k+1)).mpr
      ⟨by simpa using small,by rw [P.total];have hp : 0<mass R θ x:=pow_pos (by decide) _;omega⟩
    exact six b k shape c ci w wp sz θ hit
end R85.Original
#print axioms R85.Original.endpoints
#print axioms R85.Original.full_iff_profiles
#print axioms R85.Original.full_iff_seven
