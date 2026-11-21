import FiveBoardModel
namespace R67.Five
theorem dispatch (w : Word)
    (p0 : Proved w 0 5)
    (p1 : Proved w 0 1)
    (p2 : Proved w 0 2)
    (p3 : Proved w 0 3)
    (p4 : Proved w 0 4)
    (p5 : Proved w 1 5)
    (p6 : Proved w 1 0)
    (p7 : Proved w 1 2)
    (p8 : Proved w 1 3)
    (p9 : Proved w 1 4)
    (p10 : Proved w 2 5)
    (p11 : Proved w 2 0)
    (p12 : Proved w 2 1)
    (p13 : Proved w 2 3)
    (p14 : Proved w 2 4)
    (p15 : Proved w 3 5)
    (p16 : Proved w 3 0)
    (p17 : Proved w 3 1)
    (p18 : Proved w 3 2)
    (p19 : Proved w 3 4)
    (p20 : Proved w 4 5)
    (p21 : Proved w 4 0)
    (p22 : Proved w 4 1)
    (p23 : Proved w 4 2)
    (p24 : Proved w 4 3)
    (u h : ℕ) (hu : u<5) (hh : h=5 ∨ (h<5 ∧ h≠u)) : Proved w u h := by
  rcases (show u=0 ∨ u=1 ∨ u=2 ∨ u=3 ∨ u=4 by omega) with rfl|rfl|rfl|rfl|rfl
  · rcases hh with rfl|⟨hh,ne⟩
    · exact p0
    · rcases (show h=1 ∨ h=2 ∨ h=3 ∨ h=4 by omega) with rfl|rfl|rfl|rfl
      · exact p1
      · exact p2
      · exact p3
      · exact p4
  · rcases hh with rfl|⟨hh,ne⟩
    · exact p5
    · rcases (show h=0 ∨ h=2 ∨ h=3 ∨ h=4 by omega) with rfl|rfl|rfl|rfl
      · exact p6
      · exact p7
      · exact p8
      · exact p9
  · rcases hh with rfl|⟨hh,ne⟩
    · exact p10
    · rcases (show h=0 ∨ h=1 ∨ h=3 ∨ h=4 by omega) with rfl|rfl|rfl|rfl
      · exact p11
      · exact p12
      · exact p13
      · exact p14
  · rcases hh with rfl|⟨hh,ne⟩
    · exact p15
    · rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=4 by omega) with rfl|rfl|rfl|rfl
      · exact p16
      · exact p17
      · exact p18
      · exact p19
  · rcases hh with rfl|⟨hh,ne⟩
    · exact p20
    · rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 by omega) with rfl|rfl|rfl|rfl
      · exact p21
      · exact p22
      · exact p23
      · exact p24
end R67.Five
