import DiskCompactness
import FiveStaircaseConsequences

noncomputable section
namespace R69.Stability
open JSP404 R55.WeightedCollision Filter Topology

/-- The sole five-center input is the lower-bound component of the fixed-center result. -/
theorem five_sites {N : ℕ}
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N)) :
    SiteLaw N 5 (Jsp404.alphaN N) := by
  intro m two five c ci w wp mass θ att
  exact law ⟨m,two,five,c,ci,w,wp,mass,att⟩

theorem six_separated {N : ℕ} (ge : 3≤N)
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N)) {ε : ℝ} (ep : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤Jsp404.alphaN N-ε →
      ∃z : Fin 6→Point,(∀i,z i∈S) ∧ ∀i j,i≠j → δ*Metric.diam (S:Set Point)<dist (z i) (z j) :=
  uniform_packing ge (five_sites law) ep

theorem diameter_one_six {N : ℕ} (ge : 3≤N)
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N)) {ε : ℝ} (ep : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → Metric.diam (S:Set Point)=1 →
      maxAngle S≤Jsp404.alphaN N-ε → Separated 6 S δ := by
  obtain ⟨δ,dp,lower⟩:=six_separated ge law ep
  refine ⟨δ,dp,fun S card unit ang=>?_⟩
  simpa only [unit,mul_one,Separated] using lower S card ang

theorem five_disks_excluded {N : ℕ} (ge : 3≤N)
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N)) {ε : ℝ} (ep : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤Jsp404.alphaN N-ε →
      ∀c : Fin 5→Point,∃x∈S,∀i,δ*Metric.diam (S:Set Point)<dist x (c i) := by
  obtain ⟨δ,dp,nocover⟩:=(site_iff_disks ge _).mp (five_sites law) ε ep
  refine ⟨δ,dp,fun S card ang c=>?_⟩
  by_contra! cover
  exact nocover S card ang 5 le_rfl ⟨c,cover⟩

/-- The disk center can move, coalesce or escape; the ratio of the absolute radius
bound to the actual positive diameter is the only asymptotic scale assumption. -/
theorem five_disks_limit {N : ℕ} (ge : 3≤N)
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N))
    (S : ℕ→Finset Point) (card : ∀n,(S n).card=N) (R : ℕ→ℝ)
    (van : Tendsto (fun n=>R n/Metric.diam (S n:Set Point)) atTop (𝓝 0))
    (cover : ∀n,Disks 5 (S n) (R n)) :
    ∀ε : ℝ,0<ε → ∀ᶠ n in atTop,Jsp404.alphaN N-ε<maxAngle (S n) := by
  apply vanishing_disks ge (five_sites law) S card _ van
  intro n
  have ntr : (S n).Nontrivial:=Finset.one_lt_card_iff_nontrivial.mp (by rw [card];omega)
  have pos:=Metric.diam_pos (s:=(S n:Set Point)) ntr (S n).finite_toSet.isBounded
  rw [div_mul_cancel₀ _ pos.ne']
  exact cover n

theorem five_disks_angle_limit {N : ℕ} (ge : 3≤N)
    (law : Jsp404.alphaN N∈lowerBounds (R67.FiveConclusion.scores N))
    (S : ℕ→Finset Point) (card : ∀n,(S n).card=N) (R : ℕ→ℝ)
    (van : Tendsto (fun n=>R n/Metric.diam (S n:Set Point)) atTop (𝓝 0))
    (cover : ∀n,Disks 5 (S n) (R n)) {θ : ℝ}
    (angle : Tendsto (fun n=>maxAngle (S n)) atTop (𝓝 θ)) : Jsp404.alphaN N≤θ := by
  by_contra! bad
  let ε:=(Jsp404.alphaN N-θ)/2
  have ep : 0<ε:=by dsimp [ε];linarith
  have below : θ<Jsp404.alphaN N-ε:=by dsimp [ε];linarith
  have lower:=five_disks_limit ge law S card R van cover ε ep
  obtain ⟨n,lo,hi⟩:=(lower.and (angle.eventually_lt tendsto_const_nhds below)).exists
  exact lo.asymm hi

#print axioms five_sites
#print axioms six_separated
#print axioms diameter_one_six
#print axioms five_disks_excluded
#print axioms five_disks_limit
#print axioms five_disks_angle_limit
end R69.Stability
