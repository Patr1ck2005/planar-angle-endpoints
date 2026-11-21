import FiveHeadings
noncomputable section
namespace R64.Five
open JSP404 Real R54.GapTest R56.Windows

def chart (n : ℕ) (i : Fin 5) : Row 4 where
  w k := if h : k<4 then wall (defect n) i ⟨k,h⟩ else wall (defect n) i 0+π
  ordered := by
    intro a b ab _
    by_cases hb : b<4
    · have ha : a<4 := by omega
      simp [ha,hb]
      exact wall_mono (defect_pos n).le i (show (⟨a,ha⟩:Fin 4)≤⟨b,hb⟩ from ab)
    · by_cases ha : a<4
      · simp [ha,hb]
        have x := (arctan_mem_Ioo ((defect n)*(slope i (seq i ⟨a,ha⟩):ℝ))).2
        have y := (arctan_mem_Ioo ((defect n)*(slope i (seq i 0):ℝ))).1
        unfold wall heading
        linarith
      · simp [ha,hb]
  period := by simp

theorem chart_wall (n : ℕ) (i : Fin 5) (j : Fin 4) :
    (chart n i).w j=wall (defect n) i j := by simp [chart,j.isLt]

theorem front (n : ℕ) : Represents (chart n) (point (defect n)) := by
  intro i j ne
  obtain ⟨k,rfl⟩:=seq_cover i j ne
  refine ⟨k,k.isLt.le,?_⟩
  rw [chart_wall]
  exact bearing ne _

theorem back (n : ℕ) : Witnessed (chart n) (point (defect n)) := by
  intro i j le
  change j≤4 at le
  by_cases lt : j<4
  · let k : Fin 4:=⟨j,lt⟩
    refine ⟨seq i k,(seq_ne i k).symm,?_⟩
    change Bearing _ ((chart n i).w k)
    rw [chart_wall]
    exact bearing (seq_ne i k).symm _
  · have j4 : j=4 := by omega
    subst j
    refine ⟨seq i 0,(seq_ne i 0).symm,?_⟩
    rw [(chart n i).period]
    apply bearing_closes
    exact bearing (seq_ne i 0).symm _

private theorem internal {n : ℕ} (hn : 16≤n) (i : Fin 5) (j : Fin 4) (hj : j.val<3) :
    (chart n i).digits j (defect n)=0 := by
  let k : Fin 4 := ⟨j.val+1,by omega⟩
  let g := wall (defect n) i k-wall (defect n) i j
  have nonneg : 0≤g := sub_nonneg.mpr (wall_mono (defect_pos n).le i (show j≤k from Nat.le_succ _))
  have width:= (span_bounds (defect_pos n) (defect_small hn) i).2
  unfold span at width
  have left:=wall_mono (defect_pos n).le i (Fin.zero_le j)
  have right:=wall_mono (defect_pos n).le i (show k≤3 by omega)
  have short : g/defect n < 2 := (div_lt_iff₀ (defect_pos n)).mpr (by dsimp [g];linarith [defect_pos n])
  change ⌊((chart n i).w k-(chart n i).w j)/defect n⌋₊-1=0
  rw [chart_wall,chart_wall]
  change ⌊g/defect n⌋₊-1=0
  have fl:=Nat.floor_le (div_nonneg nonneg (defect_pos n).le)
  by_contra! bad
  have ge : 2≤⌊g/defect n⌋₊ := by omega
  have castge : (2:ℝ)≤(⌊g/defect n⌋₊:ℝ) := by exact_mod_cast ge
  linarith

private theorem external {n : ℕ} (hn : 16≤n) (i : Fin 5) :
    (chart n i).digits 3 (defect n)=n-2 := by
  let g := π-span (defect n) i
  have bounds:=span_bounds (defect_pos n) (defect_small hn) i
  have c : (16:ℝ)≤n := by exact_mod_cast hn
  have lo : ((n:ℝ)-1)≤g/defect n := (le_div_iff₀ (defect_pos n)).mpr (by dsimp [g];nlinarith only [period n,bounds.2])
  have hi : g/defect n < n := (div_lt_iff₀ (defect_pos n)).mpr (by dsimp [g];nlinarith only [period n,bounds.1,defect_pos n])
  have hh : 0≤g/defect n := by linarith
  have n1 : 1≤n := by omega
  have nf : n-1≤⌊g/defect n⌋₊ := Nat.le_floor (by simpa [Nat.cast_sub n1] using lo)
  have fl:=Nat.floor_le hh
  have nf' : ⌊g/defect n⌋₊ < n := by
    by_contra! bad
    have rr : (n:ℝ)≤(⌊g/defect n⌋₊:ℝ) := by exact_mod_cast bad
    linarith
  change ⌊((chart n i).w 4-(chart n i).w (3:ℕ))/defect n⌋₊-1=n-2
  rw [(chart n i).period]
  have g0 := chart_wall n i (0:Fin 4)
  have g3 := chart_wall n i (3:Fin 4)
  change (chart n i).w 0=_ at g0
  change (chart n i).w 3=_ at g3
  rw [g0,g3]
  have formula : wall (defect n) i 0+π-wall (defect n) i 3=g := by dsimp [g,span]; ring
  rw [formula];omega

theorem five_score {n : ℕ} (hn : 16≤n) (i : Fin 5) : score (chart n) i (defect n)=n-2 := by
  change (∑ j : Fin 4,(chart n i).digits j (defect n))=n-2
  rw [Fin.sum_univ_four,internal hn i 0 (by decide),internal hn i 1 (by decide),
    internal hn i 2 (by decide),external hn i]
  simp

#print axioms five_score
#print axioms front
#print axioms back
end R64.Five