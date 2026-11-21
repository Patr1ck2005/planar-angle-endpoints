import SendovWitness

noncomputable section
namespace R52.SendovCloud
open Real JSP404

structure FiniteCloud (k N : ℕ) (ε ρ : ℝ) where
  points : Finset Point
  piece : Fin 3 → Finset Point
  card : points.card=N
  partition : ∀ x, x∈points ↔ ∃ i, x∈piece i
  disjoint : ∀ i j, i≠j → Disjoint (piece i) (piece j)
  centers : ∀ i, center k i∈piece i
  radius : ∀ i j, i≠j → ∀ x∈piece i, dist (center k i) x<ρ*dist (center k i) (center k j)
  angle : maxAngle points<angleCap k+ε

theorem keep_labels {k N : ℕ} (lo : 3≤N) (hi : N≤5*2^k) :
    ∃ T : Finset (Label k), T.card=N ∧ ∀ i, representative k i∈T := by
  classical
  let U:=Finset.univ.image (representative k)
  have inj : Function.Injective (representative k) := fun i j h=>congrArg Sigma.fst h
  have ucard : U.card=3 := by simp [U,Finset.card_image_of_injective _ inj]
  obtain ⟨T,inc,_,size⟩:=Finset.exists_subsuperset_card_eq (Finset.subset_univ U)
    (ucard.trans_le lo) (by rw [Finset.card_univ,label_card]; exact hi)
  exact ⟨T,size,fun i=>inc (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

def fiber {k : ℕ} (T : Finset (Label k)) (f : Label k → Point) (i : Fin 3) : Finset Point :=
  (Finset.univ.filter (fun w : BinaryWord (threeClusterDims (k+2) i) =>
    (⟨i,w⟩ : Label k)∈T)).image (fun w=>f ⟨i,w⟩)

private theorem mem_fiber {k : ℕ} {T : Finset (Label k)} {f : Label k → Point} {i : Fin 3} {x : Point} :
    x∈fiber T f i ↔ ∃ w : BinaryWord (threeClusterDims (k+2) i), (⟨i,w⟩ : Label k)∈T ∧ f ⟨i,w⟩=x := by
  simp [fiber]

def Realization.trim {k N : ℕ} {ε ρ : ℝ} (R : Realization k ε ρ) (T : Finset (Label k))
    (size : T.card=N) (kept : ∀ i, representative k i∈T) : FiniteCloud k N ε ρ where
  points := T.image R.point
  piece := fiber T R.point
  card := by rwa [Finset.card_image_of_injective _ R.injective]
  partition := by
    intro x; constructor
    · intro h
      obtain ⟨⟨i,w⟩,mem,eq⟩:=Finset.mem_image.mp h
      exact ⟨i,mem_fiber.mpr ⟨w,mem,eq⟩⟩
    · rintro ⟨i,h⟩
      obtain ⟨w,mem,eq⟩:=mem_fiber.mp h
      exact Finset.mem_image.mpr ⟨⟨i,w⟩,mem,eq⟩
  disjoint := by
    intro i j ne
    apply Finset.disjoint_left.mpr
    intro x a b
    obtain ⟨u,_,hu⟩:=mem_fiber.mp a
    obtain ⟨v,_,hv⟩:=mem_fiber.mp b
    exact ne (congrArg Sigma.fst (R.injective (hu.trans hv.symm)))
  centers := fun i=>mem_fiber.mpr ⟨fun _=>false,kept i,R.fixed i⟩
  radius := by
    intro i j ne x hx
    obtain ⟨w,_,rfl⟩:=mem_fiber.mp hx
    exact R.radius ⟨i,w⟩ j ne
  angle := (maxAngle_mono (Finset.image_subset_image (Finset.subset_univ _))).trans_lt R.angle

theorem finite_clouds {k N : ℕ} (lo : 3≤N) (hi : N≤5*2^k)
    {ε ρ : ℝ} (he : 0<ε) (hr : 0<ρ) : Nonempty (FiniteCloud k N ε ρ) := by
  obtain ⟨T,size,kept⟩:=keep_labels lo hi
  obtain ⟨R⟩:=full_witness k he hr
  exact ⟨R.trim T size kept⟩

theorem full_cloud_sizes (k : ℕ) {ε ρ : ℝ} (he : 0<ε) (hr : 0<ρ) :
    ∃ F : FiniteCloud k (5*2^k) ε ρ, ∀ i, (F.piece i).card=2^threeClusterDims (k+2) i := by
  classical
  obtain ⟨R⟩:=full_witness k he hr
  let F : FiniteCloud k (5*2^k) ε ρ:=R.trim Finset.univ (by rw [Finset.card_univ,label_card]) (fun _=>Finset.mem_univ _)
  refine ⟨F,?_⟩
  intro i
  have inj : Function.Injective (fun w : BinaryWord (threeClusterDims (k+2) i) => R.point ⟨i,w⟩) := by
    intro a b e
    simpa using R.injective e
  change (fiber Finset.univ R.point i).card=_
  simp [fiber,Finset.card_image_of_injective _ inj,BinaryWord]

#print axioms finite_clouds
#print axioms full_cloud_sizes
end R52.SendovCloud

