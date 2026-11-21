import Mathlib.Tactic

/-! Exact branch-and-Farkas checker. All computation is integral; variables are nonnegative reals. -/
namespace R67.Farkas
abbrev Lin := List ℤ

def add : Lin→Lin→Lin
  | [],b=>b
  | a,[]=>a
  | x::xs,y::ys=>(x+y)::add xs ys

def scale (d : ℤ) (a : Lin) : Lin := a.map (d*·)

def unitAt (i : ℕ) (d : ℤ) : Lin := List.replicate i 0 ++ [d]

def aff (c : ℤ) (s : List (ℕ×ℤ)) : Lin :=
  s.foldr (fun p v=>add (unitAt (p.1+1) p.2) v) [c]

noncomputable def val (x : ℕ→ℝ) : Lin→ℝ
  | []=>0
  | a::as=>(a:ℝ)*x 0+ val (fun k=>x (k+1)) as

theorem val_add (x : ℕ→ℝ) (a b : Lin) : val x (add a b)=val x a+val x b := by
  induction a generalizing x b with
  | nil=>simp [val,add]
  | cons u a ih=>cases b with
    | nil=>simp [add,val]
    | cons v b=>simp only [add,val,Int.cast_add,ih];ring

theorem val_scale (x : ℕ→ℝ) (d : ℤ) (a : Lin) : val x (scale d a)=(d:ℝ)*val x a := by
  induction a generalizing x with
  | nil=>simp [val,scale]
  | cons u a ih=>simp only [scale,List.map_cons,val,Int.cast_mul];rw [show a.map (fun x=>d*x)=scale d a from rfl,ih];ring

theorem val_unit (x : ℕ→ℝ) (k : ℕ) (d : ℤ) : val x (unitAt k d)=(d:ℝ)*x k := by
  induction k generalizing x with
  | zero=>simp [unitAt,val]
  | succ k ih=>simp only [unitAt,List.replicate_succ,List.cons_append,val,Int.cast_zero,zero_mul,zero_add]
               exact ih _

theorem val_aff (x : ℕ→ℝ) (c : ℤ) (s : List (ℕ×ℤ)) : val x (aff c s)=
    (c:ℝ)*x 0+(s.map (fun p=>(p.2:ℝ)*x (p.1+1))).sum := by
  induction s with
  | nil=>simp [aff,val]
  | cons p s ih=>change val x (add _ (aff c s))=_
                 rw [val_add,val_unit,ih];simp;ring

def mix (ctx : List Lin) : List (ℕ×ℕ)→Lin
  | []=>[]
  | (i,d)::cs=>add (scale (d:ℤ) (ctx.getD i [])) (mix ctx cs)

def Good (x : ℕ→ℝ) (l : List Lin) : Prop := ∀ a∈l,0≤val x a

theorem val_mix (x : ℕ→ℝ) (ctx : List Lin) (h : Good x ctx) (cs : List (ℕ×ℕ)) :
    0≤val x (mix ctx cs) := by
  induction cs with
  | nil=>simp [mix,val]
  | cons p cs ih=>
    rw [mix,val_add,val_scale]
    have he : 0≤val x (ctx.getD p.1 []) := by
      by_cases hi : p.1<ctx.length
      · simpa only [List.getD,List.getElem?_eq_getElem hi,Option.getD_some] using h _ (List.getElem_mem hi)
      · simp [List.getD,List.getElem?_eq_none (by omega : ctx.length≤p.1),val]
    exact add_nonneg (mul_nonneg (by positivity) he) ih

def allPos (v : Lin) : Bool := v.all (0≤·)

theorem val_nonneg {x : ℕ→ℝ} (hx : ∀ k,0≤x k) {v : Lin} (h : allPos v=true) : 0≤val x v := by
  induction v generalizing x with
  | nil=>simp [val]
  | cons a l ih=>
    have ⟨ha,hm⟩ : 0≤a ∧ allPos l=true := by simpa [allPos] using h
    exact add_nonneg (mul_nonneg (by exact_mod_cast ha : 0≤(a:ℝ)) (hx _)) (ih (fun k=>hx (k+1)) hm)

theorem val_pos {x : ℕ→ℝ} (hx : ∀ k,0≤x k) (x0 : x 0=1) {v : Lin}
    (h : allPos v=true) (hp : 0<v.headD 0) : 0<val x v := by
  cases v with
  | nil=>simp at hp
  | cons a l=>
    have ⟨_,hm⟩ : 0≤a ∧ allPos l=true := by simpa [allPos] using h
    have ha : 0<(a:ℝ) := by exact_mod_cast hp
    simp only [val,x0,mul_one]
    exact add_pos_of_pos_of_nonneg ha (val_nonneg (fun k=>hx (k+1)) hm)

structure Data where
  base : List Lin
  target : Lin
  active : ℕ→Lin

inductive Cert
  | leaf (den : ℕ) (cs : List (ℕ×ℕ))
  | branch (j cut : ℕ) (left right : Cert)
deriving Inhabited

def left (j n : ℕ) := aff (n:ℤ) [(10+j,-1)]
def right (j n : ℕ) := aff (-(n:ℤ)-1) [(10+j,1)]

def check (d : Data) (ctx : List Lin) : Cert→Bool
  | .leaf den cs=>
    let v:=add (scale (den:ℤ) d.target) (scale (-1) (mix ctx cs))
    allPos v && (den>0 || v.headD 0>0)
  | .branch j cut l r=>decide (j≤16) && check d (ctx++[left j cut]) l &&
      check d (ctx++[right j cut]++(if j<16 then [d.active j] else [])) r

theorem sound (d : Data) {x : ℕ→ℝ} (hx : ∀ k,0≤x k) (x0 : x 0=1)
    (integ : ∀ j,j≤16 → ∃ m : ℕ,x ((10+j)+1)=m)
    (on : ∀ j,j<16 → 0<x ((10+j)+1) → 0≤val x (d.active j))
    (ctx : List Lin) (hc : Good x ctx) (c : Cert) (pass : check d ctx c=true) : 0≤val x d.target := by
  induction c generalizing ctx with
  | leaf den cs=>
    let v:=add (scale (den:ℤ) d.target) (scale (-1) (mix ctx cs))
    have hp : allPos v=true ∧ (0<den ∨ 0<v.headD 0) := by simpa [check,v] using pass
    have ev : val x v=(den:ℝ)*val x d.target-val x (mix ctx cs) := by simp [v,val_add,val_scale];ring
    have pos:=val_nonneg hx hp.1
    have good:=val_mix x ctx hc cs
    rcases hp.2 with hd|hd
    · rw [ev] at pos
      exact nonneg_of_mul_nonneg_right (by linarith : 0≤(den:ℝ)*val x d.target) (by exact_mod_cast hd : 0<(den:ℝ))
    · have gt:=val_pos hx x0 hp.1 hd
      rw [ev] at gt
      by_contra! bad
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤(den:ℝ)) bad.le]
  | branch j cut l r ihl ihr=>
    have pass' : (j≤16 ∧ check d (ctx++[left j cut]) l=true) ∧
        check d (ctx++[right j cut]++(if j<16 then [d.active j] else [])) r=true := by simpa [check] using pass
    obtain ⟨m,hm⟩:=integ j pass'.1.1
    by_cases lo : m≤cut
    · apply ihl _ _ pass'.1.2
      intro v hv
      rcases List.mem_append.mp hv with hv|hv
      · exact hc v hv
      · simp only [List.mem_singleton] at hv
        subst v;simp [left,val_aff,x0,hm];exact_mod_cast lo
    · apply ihr _ _ pass'.2
      intro v hv
      rcases List.mem_append.mp hv with hv|hv
      · rcases List.mem_append.mp hv with hv|hv
        · exact hc v hv
        · simp only [List.mem_singleton] at hv
          subst v;simp [right,val_aff,x0,hm];have : (cut:ℝ)+1≤m := by exact_mod_cast Nat.lt_of_not_ge lo
          linarith
      · split at hv
        next js=>simp only [List.mem_singleton] at hv;subst v;apply on j js;rw [hm];exact_mod_cast (by omega : 0<m)
        next _=>simp at hv

end R67.Farkas
#print axioms R67.Farkas.sound
