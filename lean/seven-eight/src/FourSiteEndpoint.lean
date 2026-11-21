import WeightedNormalCones
import WeightedApexFans
import OpenOrdinaryMinimum

noncomputable section
namespace R90.Endpoint
open Real JSP404 R55.WeightedCollision Finset

/-- No support of five or more distinct sites can carry more than six labels
at the 120-degree endpoint, even in the limiting weighted model. -/
theorem total_le_six {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) (five : 5≤Fintype.card I)
    (hit : 2*π/3∈attainable w c) : (∑i,w i)≤6 := by
  obtain ⟨small,v,nz,fans⟩:=R95.Heavy.physical_fans ci wp five hit
  have labels : Fintype.card I≤∑i,w i:=by
    simpa using (sum_le_sum (s:=univ) (fun i _=>show 1≤w i from wp i))
  have room (i) : (w i:ℝ)*(π/3)≤π := by
    have t : (w i:ℝ)≤2 := by exact_mod_cast small i
    nlinarith only [mul_le_mul_of_nonneg_right t pi_pos.le,pi_pos]
  have b:=R90.Aperture.weighted_fans c w (by omega) (by positivity : 0<π/3) room
    (fun i=>⟨v i,nz i,fun j ne=>fans i j ne.symm⟩)
  by_contra! large
  have n : (7:ℝ)≤(∑i,w i:ℕ):=by exact_mod_cast large
  nlinarith only [b,mul_le_mul_of_nonneg_right n pi_pos.le,pi_pos]

/-- Every limiting optimal profile for either of the original seven- and
eight-point problems has at most four distinct macroscopic sites. -/
theorem support_at_most_four {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) (many : 7≤∑i,w i) (hit : 2*π/3∈attainable w c) :
    Fintype.card I≤4 := by
  by_contra! five
  have:=total_le_six ci wp five hit
  omega

/-- A strict lower bound on every fixed weighted support of at least five
centers at all totals ≥7. -/
theorem fixed_strict {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) (many : 7≤∑i,w i) (five : 5≤Fintype.card I)
    {θ : ℝ} (hit : θ∈attainable w c) : 2*π/3<θ := by
  by_contra! small
  have atEnd:=R54.Profile.monotone hit small
  have:=total_le_six ci wp five atEnd
  omega
end R90.Endpoint
#print axioms R90.Endpoint.total_le_six
#print axioms R90.Endpoint.support_at_most_four
#print axioms R90.Endpoint.fixed_strict
