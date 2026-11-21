import CircleLift
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace R58.CircleModel
open Real JSP404

/-- A common radius around a real plane point, the ordinary definition of
concyclicity. Neither an ordering nor any angular parameters are inputs. -/
def OnCircle {I : Type*} (c : I→Point) : Prop := ∃ o : Point, ∃ r : ℝ, ∀i, dist (c i) o=r

private def continued {t : ℕ} (ht : 0<t) (v : Fin t→ℝ) (n : ℕ) : ℝ :=
  v ⟨n%t,Nat.mod_lt _ ht⟩+((n/t:ℕ):ℝ)*π

private theorem continuation {t : ℕ} (ht : 0<t) (v : Fin t→ℝ) (inc : StrictMono v)
    (range : ∀i,-π/2<v i ∧ v i≤π/2) :
    StrictMono (continued ht v) ∧
    (∀ n, continued ht v (n+t)=continued ht v n+π) ∧
    ∀i : Fin t, continued ht v i.val=v i := by
  refine ⟨?_,?_,?_⟩
  · intro a b ab
    let A : Fin t := ⟨a%t,Nat.mod_lt _ ht⟩
    let B : Fin t := ⟨b%t,Nat.mod_lt _ ht⟩
    change v A+((a/t:ℕ):ℝ)*π<v B+((b/t:ℕ):ℝ)*π
    by_cases eq : a/t=b/t
    · have ar := Nat.mod_add_div a t
      rw [eq] at ar
      have br := Nat.mod_add_div b t
      have lt : A<B := by change a%t<b%t;omega
      rw [eq]
      linarith [inc lt]
    · have lt := lt_of_le_of_ne (Nat.div_le_div_right ab.le) eq
      have gap : ((a/t:ℕ):ℝ)+1≤((b/t:ℕ):ℝ) := by exact_mod_cast lt
      nlinarith [(range A).2,(range B).1,mul_nonneg (sub_nonneg.mpr gap) pi_pos.le]
  · intro n
    simp only [continued,Nat.add_mod_right,Nat.add_div_right _ ht,Nat.cast_add,Nat.cast_one]
    ring
  · intro i
    simp [continued,Nat.mod_eq_of_lt i.isLt,Nat.div_eq_of_lt i.isLt]

/-- A finite injective planar family on a circle acquires a lifted increasing
cyclic order. The output equivalence retains the identity of every center. -/
theorem sort_circle {I : Type*} [Fintype I] [Nontrivial I] (c : I→Point) (ci : Function.Injective c)
    (circle : OnCircle c) : ∃ C : Lift (Fintype.card I), ∃ e : Fin (Fintype.card I)≃I,
      ∀ i, C.centers i=c (e i) := by
  classical
  obtain ⟨o,r,rad⟩ := circle
  obtain ⟨i,j,ij⟩ := exists_pair_ne I
  have rp : 0<r := by
    by_contra! z
    have each (i : I) : c i=o := dist_eq_zero.mp (le_antisymm ((rad i).trans_le z) dist_nonneg)
    exact ci.ne ij ((each i).trans (each j).symm)
  let E := Complex.orthonormalBasisOneI.repr.symm
  let z (i : I) := E (c i-o)
  have length (i : I) : ‖z i‖=r := by
    change ‖E (c i-o)‖=r
    rw [E.norm_map,←dist_eq_norm]
    exact rad i
  have zn (i : I) : z i≠0 := by intro h; have := length i;rw [h,norm_zero] at this;linarith
  let a (i : I) := (z i).arg/2
  have range (i : I) : -π/2<a i ∧ a i≤π/2 := by
    dsimp only [a]; constructor <;> linarith [Complex.neg_pi_lt_arg (z i),Complex.arg_le_pi (z i)]
  have plane (i : I) : c i=o+r • circleDirection (2*a i) := by
    have arg : 2*a i=(z i).arg := by dsimp [a];ring
    have parts : Complex.orthonormalBasisOneI.repr (z i)=c i-o := E.symm_apply_apply _
    have re : (z i).re=c i 0-o 0 := congrArg (fun p : Point=>p 0) parts
    have im : (z i).im=c i 1-o 1 := congrArg (fun p : Point=>p 1) parts
    rw [arg]
    ext k
    fin_cases k
    · change c i 0=o 0+r*cos (z i).arg
      rw [Complex.cos_arg (zn i),re,length]
      field_simp;ring
    · change c i 1=o 1+r*sin (z i).arg
      rw [Complex.sin_arg,im,length]
      field_simp;ring
  have ai : Function.Injective a := by
    intro i j eq
    apply ci
    rw [plane i,plane j,eq]
  let S := Finset.univ.image a
  have card : S.card=Fintype.card I := by simp [S,Finset.card_image_of_injective _ ai]
  let ord := S.orderIsoOfFin card
  let en : I≃S := Equiv.ofBijective (fun i=>⟨a i,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩) ⟨
    fun _ _ eq=>ai (congrArg Subtype.val eq),
    fun j=>by obtain ⟨i,_,eq⟩:=Finset.mem_image.mp j.property;exact ⟨i,Subtype.ext eq⟩⟩
  let e := ord.toEquiv.trans en.symm
  let v (j : Fin (Fintype.card I)) := (ord j).val
  have ve (j : Fin (Fintype.card I)) : a (e j)=v j := congrArg Subtype.val (en.apply_symm_apply (ord j))
  have inc : StrictMono v := fun _ _ lt=>ord.strictMono lt
  have rng (j) : -π/2<v j ∧ v j≤π/2 := by rw [←ve]; exact range _
  have tpos : 0<Fintype.card I := Fintype.card_pos
  obtain ⟨strict,next,start⟩ := continuation tpos v inc rng
  let C : Lift (Fintype.card I) := ⟨o,r,rp,continued tpos v,strict,next⟩
  refine ⟨C,e,?_⟩
  intro i
  change o+r • circleDirection (2*continued tpos v i.val)=c (e i)
  rw [start,←ve,←plane]

#print axioms sort_circle
end R58.CircleModel
