import FiveBoardParameter
import FiveOrbitIndex
import FiveChecked00
import FiveChecked01
import FiveChecked02
import FiveChecked03
import FiveChecked04
import FiveChecked05
import FiveChecked06
import FiveChecked07
import FiveChecked08
import FiveChecked09
import FiveChecked10
import FiveChecked11
import FiveChecked12
import FiveChecked13
import FiveChecked14
import FiveChecked15
import FiveChecked16
import FiveChecked17
import FiveChecked18
import FiveChecked19

namespace R67.Five

theorem of_mem {w : Word} (hw : w∈canonical) {u h : ℕ} (hu : u<5) (hh : h=5 ∨ (h<5 ∧ h≠u)) :
    Proved w u h := by
  simp only [canonical,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw <;> subst w
  · exact R67.FiveChecked00.all u h hu hh
  · exact R67.FiveChecked01.all u h hu hh
  · exact R67.FiveChecked02.all u h hu hh
  · exact R67.FiveChecked03.all u h hu hh
  · exact R67.FiveChecked04.all u h hu hh
  · exact R67.FiveChecked05.all u h hu hh
  · exact R67.FiveChecked06.all u h hu hh
  · exact R67.FiveChecked07.all u h hu hh
  · exact R67.FiveChecked08.all u h hu hh
  · exact R67.FiveChecked09.all u h hu hh
  · exact R67.FiveChecked10.all u h hu hh
  · exact R67.FiveChecked11.all u h hu hh
  · exact R67.FiveChecked12.all u h hu hh
  · exact R67.FiveChecked13.all u h hu hh
  · exact R67.FiveChecked14.all u h hu hh
  · exact R67.FiveChecked15.all u h hu hh
  · exact R67.FiveChecked16.all u h hu hh
  · exact R67.FiveChecked17.all u h hu hh
  · exact R67.FiveChecked18.all u h hu hh
  · exact R67.FiveChecked19.all u h hu hh

theorem all_boards {w : Word} (hw : w∈canonical) {u h k : ℕ} (hu : u<5) (hh : h=5 ∨ (h<5 ∧ h≠u))
    (hk : k≤30) (g : ℕ→ℝ) (lower : ∀j,j<10 → 0≤g j) (upper : ∀j,j<10 → g j≤2)
    (tri : ∀ a∈triComplements w,1≤total g a)
    (scores : ∀ v,v<5 → v≠u → k+weight v h≤rowSum (fun i a=>digit (total g (rowArc w i a))) v) :
    (k:ℝ)+(goal h:ℝ)/2≤total g (List.range 10) :=
  bound_digits (of_mem hw hu hh) hu hk g lower upper tri scores

theorem all_boards_unbounded {w : Word} (hw : w∈canonical) {u h k : ℕ} (hu : u<5) (hh : h=5 ∨ (h<5 ∧ h≠u))
    (g : ℕ→ℝ) (lower : ∀j,j<10 → 0≤g j) (upper : ∀j,j<10 → g j≤2)
    (tri : ∀ a∈triComplements w,1≤total g a)
    (scores : ∀ v,v<5 → v≠u → k+weight v h≤rowSum (fun i a=>digit (total g (rowArc w i a))) v) :
    (k:ℝ)+(goal h:ℝ)/2≤total g (List.range 10) :=
  bound_digits (of_mem hw hu hh) hu (le_trans (k_le_twenty hw hu g upper scores) (by decide)) g lower upper tri scores

end R67.Five
#print axioms R67.Five.all_boards
#print axioms R67.Five.all_boards_unbounded

