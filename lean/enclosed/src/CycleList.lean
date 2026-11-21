import CyclicSurgery

namespace R53.Surgery
noncomputable section

def arcPath (a : ℝ) (tail : List ℝ) (u : ℝ) : ℕ :=
  match tail with
  | [] => 2^bump a u
  | b::rest => 2^bump a b + arcPath b rest u

def cycleCapacity (l : List ℝ) : ℕ :=
  match l with
  | [] => 0
  | a::rest => 2^((l.map slot).sum) * arcPath a rest a

private theorem nonempty_path (a u : ℝ) (t : List ℝ) : 1≤arcPath a t u := by
  cases t with
  | nil => exact Nat.succ_le_of_lt (by unfold arcPath;positivity)
  | cons b t =>
    change 1≤2^bump a b+_
    exact (Nat.succ_le_of_lt (by positivity : 0<(2:ℕ)^bump a b)).trans (Nat.le_add_right _ _)

private theorem slot_join {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    slot (a+b)=slot a+slot b+bump a b := by have h:=slot_sum ha hb; unfold bump;omega

/-- A finite circular list of at least five elementary half-arcs, cut with a
maximal adjacent-pair bonus in the second position. Either merge that pair or
merge its three consecutive arcs. Both alternatives refer to the actual new
list capacity, including the wrap. Only three local comparisons with the
chosen bonus are needed. -/
theorem maximal_cut {u a b c d : ℝ} (rest : List ℝ)
    (hu : 0≤u) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (ua : 1≤u+a) (ab : 1≤a+b) (bc : 1≤b+c) (cd : 1≤c+d)
    (m₁ : bump u a≤bump a b) (m₂ : bump b c≤bump a b) (m₃ : bump c d≤bump a b) :
    cycleCapacity (u::a::b::c::d::rest) ≤ cycleCapacity (u::(a+b)::c::d::rest) ∨
    cycleCapacity (u::a::b::c::d::rest) ≤ cycleCapacity (u::(a+b+c)::d::rest) := by
  let B := slot u+(slot a+(slot b+(slot c+(slot d+(rest.map slot).sum))))
  let P := arcPath d rest u
  have one : 1≤P := nonempty_path _ _ _
  have z := slot_join ha hb
  have y := slot_join (add_nonneg ha hb) hc
  have before :
      cycleCapacity (u::a::b::c::d::rest)=
        2^B*(2^bump u a+2^bump a b+2^bump b c+2^bump c d+P) := by
    simp [cycleCapacity,arcPath,List.map_cons,B,P,Nat.add_assoc]
  have one' :
      cycleCapacity (u::(a+b)::c::d::rest)=
        2^B*(2^bump a b*(2^bump u (a+b)+2^bump (a+b) c+2^bump c d+P)) := by
    have sum : slot u+(slot (a+b)+(slot c+(slot d+(rest.map slot).sum)))=B+bump a b := by dsimp [B];omega
    simp [cycleCapacity,arcPath,List.map_cons,sum,pow_add,P,Nat.add_assoc,Nat.mul_assoc]
  have two' :
      cycleCapacity (u::(a+b+c)::d::rest)=
        2^B*(2^(bump a b+bump (a+b) c)*(2^bump u (a+b+c)+2^bump (a+b+c) d+P)) := by
    have sum : slot u+(slot (a+b+c)+(slot d+(rest.map slot).sum))=B+(bump a b+bump (a+b) c) := by dsimp [B];omega
    simp [cycleCapacity,arcPath,List.map_cons,sum,pow_add,P,Nat.add_assoc,Nat.mul_assoc]
  rw [before,one',two']
  by_cases heavy : 1≤bump a b
  · left
    apply Nat.mul_le_mul_left
    have two : 2≤2^bump c d+P := by
      have h : 0<(2:ℕ)^bump c d := by positivity
      omega
    simpa only [Nat.add_assoc] using remove_one hu ha hb hc two heavy
  · right
    apply Nat.mul_le_mul_left
    exact remove_two hu ha hb hc hd ua ab bc cd (by omega) (by omega) (by omega) (by omega) P

end
end R53.Surgery
#print axioms R53.Surgery.maximal_cut
