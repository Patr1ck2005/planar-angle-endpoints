import BoardFarkas
namespace R67.Packed
open R67.Farkas
def radix : ℤ := 4294967296

def pack : Lin→ℤ
  | []=>0
  | a::l=>a+radix*pack l

def norm : Lin→ℤ
  | []=>0
  | a::l=>|a|+norm l

theorem norm_nonneg (a : Lin) : 0≤norm a := by induction a with | nil=>rfl | cons _ _ ih=>exact add_nonneg (abs_nonneg _) ih

theorem pack_add (a b : Lin) : pack (add a b)=pack a+pack b := by
  induction a generalizing b with
  | nil=>simp [add,pack]
  | cons u a ih=>cases b with
    | nil=>simp [add,pack]
    | cons v b=>simp [add,pack,ih];ring

theorem norm_add (a b : Lin) : norm (add a b)≤norm a+norm b := by
  induction a generalizing b with
  | nil=>simp [add,norm]
  | cons u a ih=>cases b with
    | nil=>simp [add,norm]
    | cons v b=>simp only [add,norm];linarith [abs_add_le u v,ih b]

theorem pack_scale (d : ℤ) (a : Lin) : pack (scale d a)=d*pack a := by
  induction a with
  | nil=>simp [scale,pack]
  | cons u a ih=>change d*u+radix*pack (scale d a)=d*(u+radix*pack a);rw [ih];ring

theorem norm_scale (d : ℤ) (a : Lin) : norm (scale d a)=|d| * norm a := by
  induction a with
  | nil=>simp [scale,norm]
  | cons u a ih=>change |d*u|+norm (scale d a)=|d| * (|u|+norm a);rw [ih,abs_mul];ring

theorem eval_zero (x : ℕ→ℝ) (v : Lin) (small : norm v<radix) (zero : pack v=0) : val x v=0 := by
  induction v generalizing x with
  | nil=>rfl
  | cons a l ih=>
    have hn:=norm_nonneg l
    have size : |a|+norm l<4294967296 := small
    have code : a+4294967296*pack l=0 := zero
    have lo:=neg_abs_le a; have hi:=le_abs_self a
    have z : a=0 := by omega
    rw [z] at code ⊢
    simp only [val,Int.cast_zero,zero_mul,zero_add]
    exact ih _ (by simpa [norm,z,radix] using small) (by omega)

def coeffs : List (ℕ×ℕ)→ℤ
  | []=>0
  | (_,m)::cs=>(m:ℤ)+coeffs cs

def quickMix (ctx : List ℤ) : List (ℕ×ℕ)→ℤ
  | []=>0
  | (i,m)::cs=>(m:ℤ)*ctx.getD i 0+quickMix ctx cs

private theorem at_map (ctx : List Lin) (k : ℕ) : (ctx.map pack).getD k 0=pack (ctx.getD k []) := by
  by_cases h : k<ctx.length
  · simp [List.getD,List.getElem?_eq_getElem h]
  · simp [List.getD,List.getElem?_eq_none (by omega : ctx.length≤k),pack]

theorem pack_mix (ctx : List Lin) (cs : List (ℕ×ℕ)) : pack (mix ctx cs)=quickMix (ctx.map pack) cs := by
  induction cs with
  | nil=>rfl
  | cons p cs ih=>rw [mix,pack_add,pack_scale,quickMix,at_map,ih]

def Small (ctx : List Lin) : Prop := ∀a∈ctx,norm a≤256

theorem norm_mix (ctx : List Lin) (hc : Small ctx) (cs : List (ℕ×ℕ)) :
    norm (mix ctx cs)≤256*coeffs cs := by
  induction cs with
  | nil=>simp [mix,coeffs,norm]
  | cons p cs ih=>
    have h : norm (ctx.getD p.1 [])≤256 := by
      by_cases hi : p.1<ctx.length
      · simpa only [List.getD,List.getElem?_eq_getElem hi,Option.getD_some] using hc _ (List.getElem_mem hi)
      · simp [List.getD,List.getElem?_eq_none (by omega : ctx.length≤p.1),norm]
    rw [mix,coeffs]
    apply (norm_add _ _).trans
    rw [norm_scale,abs_of_nonneg (by positivity : 0≤(p.2:ℤ))]
    linarith [mul_le_mul_of_nonneg_left h (by positivity : 0≤(p.2:ℤ))]

def quick (target : ℤ) (act : ℕ→ℤ) (ctx : List ℤ) : Cert→Bool
  | .leaf den cs=>
    let t:=if den=0 then -1 else (den:ℤ)*target
    decide (quickMix ctx cs=t) && decide (256*(coeffs cs+den+1)<radix)
  | .branch j k l r=>
    decide (j≤16 ∧ k≤30) && quick target act (ctx++[pack (left j k)]) l &&
      quick target act (ctx++[pack (right j k)]++(if j<16 then [act j] else [])) r

private theorem smallLR (j k : ℕ) (hk : k≤30) : norm (left j k)≤256 ∧ norm (right j k)≤256 := by
  have nu (i : ℕ) (d : ℤ) : norm (unitAt i d)=|d| := by
    induction i with
    | zero=>simp [unitAt,norm]
    | succ i ih=>simp only [unitAt,List.replicate_succ,List.cons_append,norm,abs_zero,zero_add];exact ih
  have lc := norm_add (unitAt ((10+j)+1) (-1)) [(k:ℤ)]
  have rc := norm_add (unitAt ((10+j)+1) 1) [-(k:ℤ)-1]
  simp only [nu,norm,abs_neg,abs_one,abs_of_nonneg (Int.natCast_nonneg _),add_zero] at lc rc
  change norm (add (unitAt ((10+j)+1) (-1)) [(k:ℤ)])≤256 ∧ norm (add (unitAt ((10+j)+1) 1) [-(k:ℤ)-1])≤256
  have : |-(k:ℤ)-1|=(k:ℤ)+1 := by rw [abs_of_nonpos (by omega)];omega
  rw [this] at rc
  exact ⟨by omega, by omega⟩

theorem sound (d : Data) {x : ℕ→ℝ} (_hx : ∀ k,0≤x k) (x0 : x 0=1)
    (integ : ∀ j,j≤16 → ∃ m : ℕ,x ((10+j)+1)=m)
    (on : ∀ j,j<16 → 0<x ((10+j)+1) → 0≤val x (d.active j))
    (ns : norm d.target≤256) (na : ∀j,j<16 → norm (d.active j)≤256)
    (ctx : List Lin) (hc : Good x ctx) (nc : Small ctx)
    (c : Cert) (pass : quick (pack d.target) (pack ∘ d.active) (ctx.map pack) c=true) : 0≤val x d.target := by
  induction c generalizing ctx with
  | leaf den cs=>
    have p : quickMix (ctx.map pack) cs=(if den=0 then -1 else (den:ℤ)*pack d.target) ∧
        256*(coeffs cs+den+1)<radix := by simpa [quick] using pass
    let t : Lin := if den=0 then [-1] else scale (den:ℤ) d.target
    let r := add t (scale (-1) (mix ctx cs))
    have eq : pack r=0 := by
      simp only [r,pack_add,pack_scale,pack_mix,p.1,t];split <;> simp [pack,pack_scale]
    have nt : norm t≤256*((den:ℤ)+1) := by
      dsimp only [t];split
      next z=>simp [z,norm]
      next nz=>rw [norm_scale,abs_of_nonneg (by positivity : 0≤(den:ℤ))]
               linarith [mul_le_mul_of_nonneg_left ns (by positivity : 0≤(den:ℤ))]
    have small : norm r<radix := by
      have z:=norm_add t (scale (-1) (mix ctx cs))
      rw [norm_scale] at z;norm_num at z
      dsimp [r];linarith [norm_mix ctx nc cs,p.2]
    have ev := eval_zero x r small eq
    simp only [r,val_add,val_scale,Int.cast_neg,Int.cast_one,neg_one_mul] at ev
    have good:=val_mix x ctx hc cs
    by_cases z : den=0
    · simp [t,z,val,x0] at ev;linarith
    · simp [t,z,val_scale] at ev
      exact nonneg_of_mul_nonneg_right (by linarith : 0≤(den:ℝ)*val x d.target) (by exact_mod_cast (Nat.pos_of_ne_zero z))
  | branch j cut l r ihl ihr=>
    have p : ((j≤16 ∧ cut≤30) ∧ quick (pack d.target) (pack ∘ d.active) ((ctx++[left j cut]).map pack) l=true) ∧
       quick (pack d.target) (pack ∘ d.active) ((ctx++[right j cut]++(if j<16 then [d.active j] else [])).map pack) r=true := by
      by_cases hj : j<16 <;> simpa [quick,hj,Function.comp_def] using pass
    obtain ⟨m,hm⟩:=integ j p.1.1.1
    have sn:=smallLR j cut p.1.1.2
    by_cases lo : m≤cut
    · apply ihl _ _ _ p.1.2
      · intro v hv
        rcases List.mem_append.mp hv with hv|hv
        · exact hc v hv
        · simp only [List.mem_singleton] at hv
          subst v;simp [left,val_aff,x0,hm];exact_mod_cast lo
      · simpa [Small,or_imp,forall_and] using And.intro nc sn.1
    · apply ihr _ _ _ p.2
      · intro v hv
        rcases List.mem_append.mp hv with hv|hv
        · rcases List.mem_append.mp hv with hv|hv
          · exact hc v hv
          · simp only [List.mem_singleton] at hv
            subst v;simp [right,val_aff,x0,hm];have : (cut:ℝ)+1≤m := by exact_mod_cast Nat.lt_of_not_ge lo
            linarith
        · split at hv
          next js=>simp only [List.mem_singleton] at hv;subst v;apply on j js;rw [hm];exact_mod_cast (by omega : 0<m)
          next _=>simp at hv
      · by_cases hj : j<16
        · simpa [Small,hj,or_imp,forall_and] using And.intro nc (And.intro sn.2 (na j hj))
        · simpa [Small,hj,or_imp,forall_and] using And.intro nc sn.2

end R67.Packed
#print axioms R67.Packed.sound
