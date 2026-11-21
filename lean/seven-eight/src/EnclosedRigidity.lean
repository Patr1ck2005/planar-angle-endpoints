import EnclosedSharp
import InteriorFourRigidity
import InteriorRigidity

noncomputable section
namespace R89.Sharp
open Real JSP404 R55.WeightedCollision

/-- Every support attaining the sharp cap at an enclosed site has precisely
three other sites. Their weights are arbitrary. -/
theorem equality_four {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀j,0<w j) (i : I)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) (hit : criticalAngle (w i)∈attainable w c) :
    Fintype.card I=4 := by
  by_cases big : 2≤w i
  · exact R93.Interior.endpoint_card_four ci wp i big inside hit
  · have one : w i=1:=by have:=wp i;omega
    have mac:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
    have eq : criticalAngle (w i)=2*π/3 := by rw [one];simp [criticalAngle];ring
    rw [eq] at mac
    exact R91.Rigid.four_sites ci inside mac.2.1

/-- Each fixed support of at least five sites has a strict gap above the
four-site optimum for any positive multiplicity at its enclosed site. -/
theorem strict_enclosed {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀j,0<w j) (i : I)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) (many : 5≤Fintype.card I)
    {θ : ℝ} (hit : θ∈attainable w c) : criticalAngle (w i)<θ := by
  apply lt_of_le_of_ne (R89.Interior.enclosed_angle ci wp hit i inside)
  intro eq
  have tight : criticalAngle (w i)∈attainable w c:=by
    change criticalAngle (w i)=θ at eq
    rwa [eq]
  have:=equality_four ci wp i inside tight
  omega
end R89.Sharp
#print axioms R89.Sharp.equality_four
#print axioms R89.Sharp.strict_enclosed
