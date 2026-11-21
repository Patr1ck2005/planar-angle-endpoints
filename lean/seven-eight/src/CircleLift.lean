import CircleChord
import FixedCenterGap
import Mathlib.Data.Nat.Periodic

noncomputable section
namespace R58.CircleModel
open Real JSP404 InnerProductGeometry R54.GapTest R56.Windows

/-- A lifted cyclic ordering of the angular half-arguments on an actual circle. -/
structure Lift (t : ℕ) where
  center : Point
  radius : ℝ
  pos : 0<radius
  u : ℕ→ℝ
  increasing : StrictMono u
  nextPeriod : ∀ n, u (n+t)=u n+π

namespace Lift
variable {t : ℕ} (C : Lift t)
def P (n : ℕ) : Point := C.center+C.radius • circleDirection (2*C.u n)
def centers (i : Fin t) : Point := C.P i.val

theorem periodic : Function.Periodic C.P t := by
  intro n
  have e : 2*C.u (n+t)=2*C.u n+2*π := by rw [C.nextPeriod];ring
  have turn (v : ℝ) : circleDirection (v+2*π)=circleDirection v := by
    ext i;fin_cases i <;> simp [circleDirection]
  simp only [P,e,turn]

def index (ht : 0<t) (n : ℕ) : Fin t := ⟨n%t,Nat.mod_lt _ ht⟩
theorem center_index (ht : 0<t) (n : ℕ) : C.centers (index ht n)=C.P n :=
  C.periodic.map_mod_nat n

/-- The actual forward chord, with its positive length factor, including any
nontrivial rotation or translation of the circle. -/
theorem chord {n k : ℕ} (nk : n<k) (kw : k<n+t) :
    ∃r : ℝ,0<r ∧ C.P k-C.P n=r • circleDirection (C.u n+C.u k+π/2) := by
  have lt := C.increasing nk
  have high := C.increasing kw
  rw [C.nextPeriod] at high
  change C.u k<C.u n+π at high
  let a := 2*C.u n
  let b := 2*C.u k
  have sp := Sendov.CircleChord.chord_scale_pos (u:=a) (v:=b)
    (by dsimp [a,b];linarith) (by dsimp [a,b];linarith)
  refine ⟨_,mul_pos C.pos sp,?_⟩
  have e := Sendov.CircleChord.chord_factor a b
  rw [Sendov.CircleChord.tangent_eq_point_quarter] at e
  have av : (b+a)/2+π/2=C.u n+C.u k+π/2 := by dsimp [a,b];ring
  rw [av] at e
  change circleDirection b-circleDirection a=_ at e
  change (C.center+C.radius • circleDirection b)-(C.center+C.radius • circleDirection a)=_
  rw [add_sub_add_left_eq_sub,←smul_sub,e,smul_smul]
  rfl

theorem point_ne {n k : ℕ} (nk : n<k) (kw : k<n+t) : C.P n≠C.P k := by
  obtain ⟨r,rp,eq⟩ := C.chord nk kw
  intro e
  rw [e,sub_self] at eq
  have nz : circleDirection (C.u n+C.u k+π/2)≠0 := by
    intro z
    have h := norm_circleDirection (C.u n+C.u k+π/2)
    simp [z] at h
  exact (smul_ne_zero rp.ne' nz) eq.symm

theorem centers_injective : Function.Injective C.centers := by
  intro i j e
  by_contra ne
  have sep : i.val≠j.val := fun h=>ne (Fin.ext h)
  rcases lt_or_gt_of_ne sep with h|h
  · exact C.point_ne h (by omega) e
  · exact C.point_ne h (by omega) e.symm

theorem wall {n k : ℕ} (nk : n<k) (kw : k<n+t) :
    Bearing (C.P k-C.P n) (C.u n+C.u k+π/2) := by
  obtain ⟨r,rp,h⟩ := C.chord nk kw
  exact ⟨r,rp,1,Or.inr rfl,by simpa only [one_smul] using h⟩

/-- The triangle of three successive actual circle points supplies the arc
legality used in the cyclic extremum. -/
theorem corner (ht : 3≤t) (n : ℕ) :
    EuclideanGeometry.angle (C.P n) (C.P (n+1)) (C.P (n+2))=π-(C.u (n+2)-C.u n) := by
  obtain ⟨r,rp,h⟩ := C.chord (n:=n) (k:=n+1) (by omega) (by omega)
  obtain ⟨s,sp,g⟩ := C.chord (n:=n+1) (k:=n+2) (by omega) (by omega)
  have dif : 0≤C.u (n+2)-C.u n := sub_nonneg.mpr (C.increasing.monotone (by omega))
  have bound := C.increasing (show n+2<n+t by omega)
  rw [C.nextPeriod] at bound
  change angle (C.P n-C.P (n+1)) (C.P (n+2)-C.P (n+1))=_
  rw [←neg_sub (C.P (n+1)) (C.P n),h,g,angle_neg_left,angle_smul_left_of_pos _ _ rp,
    angle_smul_right_of_pos _ _ sp,angle_circleDirection]
  rw [show C.u n+C.u (n+1)+π/2-(C.u (n+1)+C.u (n+2)+π/2) = -(C.u (n+2)-C.u n) by ring,
    cos_neg,arccos_cos dif (by linarith)]

#print axioms chord
#print axioms centers_injective
#print axioms corner
end Lift
end R58.CircleModel
