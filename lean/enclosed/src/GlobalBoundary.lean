import ProfileMinimum
import AttainedProfile
noncomputable section
namespace R54.Profile
open JSP404 R55.WeightedCollision R56.Decorated Real

def Normalized {I : Type*} (c : I→Point) := (∀ i,dist (c i) 0≤1) ∧
  (∀ i j,dist (c i) (c j)≤1) ∧ ∃ i j,dist (c i) (c j)=1

/-- Finite macrocenters with enough mutually compatible binary axes to carry N
ordinary labels. The bound on m and diameter normalization also hold at a minimum. -/
def decoratedScores (N : ℕ) : Set ℝ := {θ | ∃ m : ℕ,2≤m ∧ m≤N ∧
  ∃ c : Fin m→Point,Function.Injective c ∧ Normalized c ∧
  ∃ d : Fin m→ℕ,N≤∑ i,2^(d i) ∧ 0≤θ ∧
    (∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤θ) ∧ Nonempty (Axes c d θ)}

theorem fin_other {m : ℕ} (mg : 2≤m) (i : Fin m) : ∃ j,j≠i := by
  let a : Fin m:=⟨0,by omega⟩
  let b : Fin m:=⟨1,by omega⟩
  by_cases h : i=a
  · exact ⟨b,by rw [h];intro eq;exact Nat.one_ne_zero (congrArg Fin.val eq)⟩
  · exact ⟨a,Ne.symm h⟩

theorem count_le_total {m N : ℕ} {w : Fin m→ℕ} (hw : ∀ i,0<w i) (sz : ∑ i,w i=N) : m≤N := by
  have h : (∑ _ : Fin m,(1:ℕ))≤∑ i,w i := Finset.sum_le_sum (fun i _=>Nat.succ_le_of_lt (hw i))
  simpa [sz] using h

theorem realized_minimum {N : ℕ} (ge : 3≤N) :
    ∃ m : ℕ,2≤m ∧ m≤N ∧ ∃ c : Fin m→Point,Function.Injective c ∧ Normalized c ∧
      ∃ w : Fin m→ℕ,(∀ i,0<w i) ∧ (∑ i,w i)=N ∧ minimum w c=alpha N ∧
        Admissible w c (alpha N) := by
  obtain ⟨m,mg,c,ci,cb,cd,ends,w,hw,sz,profile⟩:=R57.Compact.attained_profile ge
  have other:=fin_other mg
  have mc:=count_le_total hw sz
  have p : alpha N∈attainable w c := profile
  have lo:=alpha_bound (sz.symm ▸ ge) (fixed_minimum hw other ci).1.1
  rw [sz] at lo
  exact ⟨m,mg,mc,c,ci,⟨cb,cd,ends⟩,w,hw,sz,le_antisymm ((fixed_minimum hw other ci).1.2 p) lo,
    (fixed_profile hw other ci).mp p⟩

theorem decorated_minimum {N : ℕ} (ge : 3≤N) : IsLeast (decoratedScores N) (alpha N) := by
  constructor
  · obtain ⟨m,mg,c,ci,cb,cd,ends,w,hw,sz,profile⟩:=R57.Compact.attained_profile ge
    have two:=fin_other mg
    have mc:=count_le_total hw sz
    obtain ⟨pos,cap,A,_⟩:=necessary hw two ci profile
    refine ⟨m,mg,mc,c,ci,⟨cb,cd,ends⟩,_,?_,pos,cap,⟨A⟩⟩
    rw [←sz]
    exact Finset.sum_le_sum (fun i _=>Nat.le_pow_clog (by decide : 1<2) (w i))
  · rintro θ ⟨m,_,_,c,ci,_,d,sz,pos,cap,⟨A⟩⟩
    exact (alpha_mono ge sz).trans (alpha_lift ci pos (ge.trans sz) cap A)

/-- Full lower bounds are equivalent to a finite capacity exclusion at every
smaller angular threshold. Equality at the sharp threshold does not have to be excluded. -/
theorem lower_iff {N : ℕ} (ge : 3≤N) (θ : ℝ) :
    θ≤alpha N ↔ ∀ t∈decoratedScores N, θ≤t :=
  ⟨fun h _ ht=>h.trans ((decorated_minimum ge).2 ht),fun h=>h _ (decorated_minimum ge).1⟩

end R54.Profile
#print axioms R54.Profile.realized_minimum
#print axioms R54.Profile.decorated_minimum
#print axioms R54.Profile.lower_iff
