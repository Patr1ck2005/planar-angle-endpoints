import FiveCenterPublic
import SixMarked

noncomputable section
namespace R85.Seven
open JSP404 R55.WeightedCollision R54.GapTest R56.Windows R69.Stability

/-- The six-site statement at one ordinary cardinality, retaining that cardinality in the hypotheses. -/
def SixAt (N : ℕ) : Prop :=
  ∀ (c : Fin 6 → Point), Function.Injective c → ∀ (w : Fin 6 → ℕ),
    (∀ i, 0 < w i) → (∑ i, w i) = N → ∀ θ ∈ attainable w c, Jsp404.alphaN N ≤ θ

theorem site_law {N : ℕ} (ge : 3 ≤ N) (six : SixAt N) :
    SiteLaw N 6 (Jsp404.alphaN N) := by
  intro m two sm c ci w wp eq θ hit
  by_cases five : m ≤ 5
  · exact (R67.FiveCenter.sharp ge).2 ⟨m,two,five,c,ci,w,wp,eq,hit⟩
  · obtain rfl : m=6 := by omega
    exact six c ci w wp eq _ hit

/-- A fixed angular deficit gives seven ordinary points separated on the diameter scale. -/
theorem separated {N : ℕ} (ge : 3 ≤ N) (six : SixAt N) {ε : ℝ} (pos : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset Point, S.card = N →
      maxAngle S ≤ Jsp404.alphaN N - ε → Separated 7 S (δ * Metric.diam (S : Set Point)) :=
  uniform_packing ge (site_law ge six) pos

/-- The seven-site conclusion is unconditional in the two proven upper parts of the weight bands. -/
theorem bands {N k : ℕ}
    (band : (9*2^k < 2*N ∧ N ≤ 5*2^k) ∨ (6*2^k < N ∧ N ≤ 8*2^k)) :
    SixAt N := by
  intro c ci w wp eq θ hit
  subst N
  rcases band with low|high
  · exact R80.Six.low_top ci wp hit low.1 low.2
  · exact R80.Six.high_top ci wp hit high.1 high.2

theorem separated_bands {N k : ℕ}
    (band : (9*2^k < 2*N ∧ N ≤ 5*2^k) ∨ (6*2^k < N ∧ N ≤ 8*2^k))
    {ε : ℝ} (pos : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset Point, S.card = N →
      maxAngle S ≤ Jsp404.alphaN N - ε → Separated 7 S (δ * Metric.diam (S : Set Point)) := by
  have hp := Nat.two_pow_pos k
  have ge : 3 ≤ N := by rcases band with a|a <;> omega
  exact separated ge (bands band) pos

/-- Only proper-retention-critical, nonconcyclic configurations on seven or more
sites are needed after the six-site lower bound at N is supplied. -/
theorem unrestricted_iff {N : ℕ} (ge : 3 ≤ N) (six : SixAt N) :
    alpha N=Jsp404.alphaN N ↔
      ∀{k : ℕ},7≤k→k≤N→∀(c : Fin k→Point),Function.Injective c→
      ¬R58.CircleModel.OnCircle c→∀θ : ℝ,0≤θ→θ<Real.pi→Macro c θ→
      (∃m : Fin k→ℕ,∃R : ∀i,Row (m i),Represents R c ∧ Witnessed R c ∧ N≤R65.Retention.capacity R θ)→
      R65.Retention.Critical c N θ→Jsp404.alphaN N≤θ := by
  rw [R67.FiveCenter.unrestricted_iff_six ge]
  constructor
  · intro all k seven; exact all (by omega)
  · intro all k lo hi c ci circ θ nn lt mac system critical
    by_cases seven : 7≤k
    · exact all seven hi c ci circ θ nn lt mac system critical
    obtain rfl : k=6 := by omega
    obtain ⟨m,R,front,back,room⟩:=system
    obtain ⟨w,wp,eq,att⟩:=(R65.Retention.positive_mass_iff ci R front back nn lt mac N).mpr
      ⟨by simpa using hi,room⟩
    exact six c ci w wp eq θ att
end R85.Seven
#print axioms R85.Seven.site_law
#print axioms R85.Seven.separated
#print axioms R85.Seven.bands
#print axioms R85.Seven.separated_bands
#print axioms R85.Seven.unrestricted_iff
