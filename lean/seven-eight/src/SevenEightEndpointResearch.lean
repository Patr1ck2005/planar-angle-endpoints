import EndpointShapes
import EquilateralInterior
import SevenFourCenters
import FiveSeparatedEndpoint
import EightPointClusters

noncomputable section
namespace R90.Endpoint
open Real JSP404 R55.WeightedCollision

/-- The complete seven-label endpoint shape, including the geometry of
the four-site alternative and each site's multiplicity. -/
theorem seven_geometry {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i)
    (seven : (∑i,w i)=7) (hit : 2*π/3∈attainable w c) :
    (∃e : Fin 2≃I,w (e 0)=3 ∧ w (e 1)=4) ∨
    (Fintype.card I=4 ∧ ∃i,w i=1 ∧ c i∈convexHull ℝ (c '' {j | j≠i}) ∧
      ∃h : Fin 3↪I,(∀a,h a≠i ∧ w (h a)=2) ∧ (∀j,j≠i→∃a,h a=j) ∧
        (∀a b,a≠b→EuclideanGeometry.angle (c (h a)) (c i) (c (h b))=2*π/3) ∧
        (∀a b d,a≠b→a≠d→b≠d→EuclideanGeometry.angle (c (h a)) (c (h b)) (c (h d))=π/3) ∧
        (∀a b d,a≠b→a≠d→b≠d→dist (c (h a)) (c (h b))=dist (c (h a)) (c (h d))) ∧
        ∀a b,dist (c (h a)) (c i)=dist (c (h b)) (c i)) := by
  obtain two|⟨four,i,inside,one,outer⟩:=seven_shape ci wp seven hit
  · exact Or.inl two
  obtain ⟨h,other,surj,angles,triangle,sides,radii⟩:=
    R96.Endpoint.seven_shape ci wp four hit i inside seven
  exact Or.inr ⟨four,i,one,inside,h,fun a=>⟨other a,outer _ (other a)⟩,surj,angles,triangle,sides,radii⟩
end R90.Endpoint
