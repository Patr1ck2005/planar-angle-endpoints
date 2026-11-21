import FiveStaircaseConsequences
import OrbitCapacity
import RawBoardMacro
import FiveCanonicalWords
noncomputable section
namespace R67.Final
open R67 R67.Board R67.OrderOrbit R68.Raw
def RepresentativeCoverage : Prop := ∀o : Equiv.Perm E, OrientOK o→∃w : Sym,
  representativeWord w.r∈Five.canonical ∧ MaskLaw w (actualWord o)
def AllCertificates : Prop := ∀ word∈Five.canonical,∀u h : ℕ,u<5→(h=5 ∨ h<5 ∧ h≠u)→Five.Proved word u h

theorem finite_board_law (coverage : RepresentativeCoverage) (cert : AllCertificates) : FiniteBoardLaw := by
  intro o ori g box mac k small u p apart marks
  obtain ⟨w,member,sym⟩:=coverage o ori
  have macroFit:= (R68.Raw.macro_iff o ori g (sample g) (sample_val g)).mp mac
  apply orbit_capacity w (actualWord o) sym (cert _ member) u p apart k (by omega) g box macroFit
  intro i ne
  have h:=marks i ne
  rw [R68.Raw.row_score o g (sample g) (sample_val g) i] at h
  exact h
#print axioms finite_board_law
end R67.Final
