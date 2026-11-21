import SendovClouds
import ThreeCoverDefs

noncomputable section
namespace R52.SendovCloud
open Real JSP404 R52.ThreeCover

/-- A single baseline is selected from the three fixed representatives and
works for every approximation tolerance. -/
theorem longest_baseline (k : ℕ) : ∃ i j : Fin 3, i≠j ∧
    ∀ x y : Fin 3, dist (center k x) (center k y)≤dist (center k i) (center k j) := by
  classical
  obtain ⟨m,_,hm⟩:=Finset.exists_max_image Finset.univ
    (fun z : Fin 3 × Fin 3=>dist (center k z.1) (center k z.2)) Finset.univ_nonempty
  have pos : 0<dist (center k 0) (center k 1) := dist_pos.mpr
    ((threeClusterCenters_injective (k+2)).ne (by decide : (0 : Fin 3)≠1))
  have hd:=pos.trans_le (hm (0,1) (Finset.mem_univ _))
  refine ⟨m.1,m.2,?_,fun x y=>hm (x,y) (Finset.mem_univ _)⟩
  intro eq
  simpa [eq] using hd

theorem FiniteCloud.covered {k N : ℕ} {ε ρ : ℝ} (F : FiniteCloud k N ε ρ) (hr : 0≤ρ) :
    Covered F.points ρ := by
  obtain ⟨i,j,ne,big⟩:=longest_baseline k
  have mem (z : Fin 3) : center k z∈F.points := (F.partition _).2 ⟨z,F.centers z⟩
  refine ⟨center k i,mem i,center k j,mem j,(threeClusterCenters_injective _).ne ne,center k,?_⟩
  intro x hx
  obtain ⟨z,hz⟩:=(F.partition x).1 hx
  obtain ⟨u,une⟩:=exists_ne z
  refine ⟨z,?_⟩
  rw [dist_comm x]
  exact (F.radius z u une.symm x hz).le.trans (mul_le_mul_of_nonneg_left (big z u) hr)

theorem cap_source (k : ℕ) : angleCap k=π-2*π/(2*(k:ℝ)+5) := by
  rw [cap_formula]; ring

theorem mem_scores {k N : ℕ} (lo : 3≤N) (hi : N≤5*2^k) :
    π-2*π/(2*(k:ℝ)+5)∈scores N := by
  intro δ hd
  obtain ⟨F⟩:=finite_clouds lo hi hd hd
  exact ⟨F.points,F.card,(cap_source k) ▸ F.angle,F.covered hd.le⟩

#print axioms mem_scores
end R52.SendovCloud

