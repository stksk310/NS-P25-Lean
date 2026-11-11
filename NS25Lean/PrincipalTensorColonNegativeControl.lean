import NS25Lean.NumericalSemigroupBasic
import Mathlib.Tactic

set_option linter.style.header false
namespace NS25Lean.PrincipalTensorColonNegativeControl

/-- Exact Apéry thresholds modulo 8, established below by coefficient witnesses. -/
def threshold : ℕ → ℕ
  | 0 => 0 | 1 => 41 | 2 => 26 | 3 => 43
  | 4 => 28 | 5 => 13 | 6 => 30 | _ => 15

def inH (n : ℕ) : Prop := threshold (n%8) ≤ n
instance (n : ℕ) : Decidable (inH n) := inferInstanceAs (Decidable (_≤_))

 theorem add8 {n : ℕ} (hn : inH n) : inH (n+8) := by
  unfold inH at *
  simpa only [Nat.add_mod_right] using (show threshold (n%8) ≤ n+8 by omega)

 theorem add13 {n : ℕ} (hn : inH n) : inH (n+13) := by
  unfold inH at *
  have hr : n%8<8 := Nat.mod_lt _ (by decide)
  generalize he : n%8=r at hn hr
  interval_cases r <;> simp_all [Nat.add_mod,threshold] <;> omega

 theorem add15 {n : ℕ} (hn : inH n) : inH (n+15) := by
  unfold inH at *
  have hr : n%8<8 := Nat.mod_lt _ (by decide)
  generalize he : n%8=r at hn hr
  interval_cases r <;> simp_all [Nat.add_mod,threshold] <;> omega

 theorem coefficients_mem (x y z : ℕ) : inH (8*x+13*y+15*z) := by
  induction x with
  | zero =>
    induction y with
    | zero =>
      induction z with
      | zero => decide
      | succ z hz => convert add15 hz using 1 <;> omega
    | succ y hy => convert add13 hy using 1 <;> omega
  | succ x hx => convert add8 hx using 1 <;> omega

/-- No truncation or sampled membership oracle: every member has a genuine
three-generator decomposition, and every such decomposition is a member. -/
 theorem membership_iff_coefficients (n : ℕ) :
    inH n ↔ ∃ x y z : ℕ, n=8*x+13*y+15*z := by
  constructor
  · intro hn
    unfold inH at hn
    have hr : n%8<8 := Nat.mod_lt _ (by decide)
    have hdiv := Nat.mod_add_div n 8
    generalize he : n%8=r at hn hr
    interval_cases r <;> simp_all [threshold]
    · exact ⟨n/8,0,0,by omega⟩
    · exact ⟨n/8-5,2,1,by omega⟩
    · exact ⟨n/8-3,2,0,by omega⟩
    · exact ⟨n/8-5,1,2,by omega⟩
    · exact ⟨n/8-3,1,1,by omega⟩
    · exact ⟨n/8-1,1,0,by omega⟩
    · exact ⟨n/8-3,0,2,by omega⟩
    · exact ⟨n/8-1,0,1,by omega⟩
  · rintro ⟨x,y,z,rfl⟩
    exact coefficients_mem x y z

 theorem add_mem {n m : ℕ} (hn : inH n) (hm : inH m) : inH (n+m) := by
  obtain ⟨x,y,z,rfl⟩ := (membership_iff_coefficients n).mp hn
  obtain ⟨u,v,w,rfl⟩ := (membership_iff_coefficients m).mp hm
  convert coefficients_mem (x+u) (y+v) (z+w) using 1 <;> omega

 theorem conductor (n : ℕ) (hn : 36≤n) : inH n := by
  unfold inH
  have hr : n%8<8 := Nat.mod_lt _ (by decide)
  generalize he : n%8=r at hr
  interval_cases r <;> simp_all [threshold] <;> omega

 def H : NumericalSemigroup where
  toAddSubmonoid := {
    carrier := {n | inH n}
    zero_mem' := by decide
    add_mem' := fun ha hb => add_mem ha hb }
  finite_compl := (Set.finite_Iio 36).subset (by intro n hn; exact lt_of_not_ge (fun h => hn (conductor n h)))

/-- The displayed generators generate the actual numerical semigroup H. -/
theorem H_generated : H.IsGeneratedByThree 8 13 15 := by
  unfold NumericalSemigroup.IsGeneratedByThree NumericalSemigroup.generatedBy
  apply le_antisymm
  · intro n hn
    obtain ⟨x,y,z,he⟩ := (membership_iff_coefficients n).mp hn
    have h8 : 8∈AddSubmonoid.closure ({8,13,15}:Set ℕ) := AddSubmonoid.subset_closure (by simp)
    have h13 : 13∈AddSubmonoid.closure ({8,13,15}:Set ℕ) := AddSubmonoid.subset_closure (by simp)
    have h15 : 15∈AddSubmonoid.closure ({8,13,15}:Set ℕ) := AddSubmonoid.subset_closure (by simp)
    have hh := (AddSubmonoid.closure ({8,13,15}:Set ℕ)).add_mem
      ((AddSubmonoid.closure ({8,13,15}:Set ℕ)).add_mem
        ((AddSubmonoid.closure ({8,13,15}:Set ℕ)).nsmul_mem h8 x)
        ((AddSubmonoid.closure ({8,13,15}:Set ℕ)).nsmul_mem h13 y))
      ((AddSubmonoid.closure ({8,13,15}:Set ℕ)).nsmul_mem h15 z)
    rw [he]
    simpa [nsmul_eq_mul,Nat.mul_comm] using hh
  · apply AddSubmonoid.closure_le.mpr
    intro n hn
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl <;> change inH _ <;> decide

/-- Exact coefficient normalization of Γ=<20,24,39,45> with three-tail gcd 3. -/
theorem gamma_normalization (n : ℕ) :
    (∃ q h, inH h ∧ n=20*q+3*h) ↔
      ∃ q x y z, n=20*q+24*x+39*y+45*z := by
  constructor
  · rintro ⟨q,h,hh,he⟩
    obtain ⟨x,y,z,hxyz⟩ := (membership_iff_coefficients h).mp hh
    exact ⟨q,x,y,z,by omega⟩
  · rintro ⟨q,x,y,z,he⟩
    exact ⟨q,8*x+13*y+15*z,coefficients_mem x y z,by omega⟩

theorem gamma_minimal_four :
    (¬∃x y z:ℕ,20=24*x+39*y+45*z) ∧
    (¬∃x y z:ℕ,24=20*x+39*y+45*z) ∧
    (¬∃x y z:ℕ,39=20*x+24*y+45*z) ∧
    (¬∃x y z:ℕ,45=20*x+24*y+39*z) := by omega

theorem tail_normalization_gcd : Nat.gcd 24 (Nat.gcd 39 45)=3 ∧ Nat.gcd 20 3=1 := by decide

/-- The only small return is 20; the principal return is 2*20=40. -/
def oldIdeal (n : ℕ) : Prop := inH n ∧ 20≤n ∧ inH (n-20)
def newIdeal (n : ℕ) : Prop := oldIdeal n ∨ (40≤n ∧ inH (n-40))
instance (n : ℕ) : Decidable (oldIdeal n) := inferInstanceAs (Decidable (_∧_))
instance (n : ℕ) : Decidable (newIdeal n) := inferInstanceAs (Decidable (_∨_))

 theorem first_principal_index : ¬inH 20 ∧ inH (2*20) := by decide
 theorem old_tail (n : ℕ) (hn : 56≤n) : oldIdeal n :=
  ⟨conductor n (by omega),by omega,conductor (n-20) (by omega)⟩
 theorem old_closed {n d : ℕ} (hn : oldIdeal n) (hd : inH d) : oldIdeal (n+d) := by
  have hge := hn.2.1
  refine ⟨add_mem hn.1 hd,by omega,?_⟩
  convert add_mem hn.2.2 hd using 1 <;> omega
 theorem new_closed {n d : ℕ} (hn : newIdeal n) (hd : inH d) : newIdeal (n+d) := by
  rcases hn with hn | hn
  · exact Or.inl (old_closed hn hd)
  · refine Or.inr ⟨by omega,?_⟩
    convert add_mem hn.2 hd using 1 <;> omega
 theorem new_mem_H {n : ℕ} (hn : newIdeal n) : inH n := by
  rcases hn with hn | hn
  · exact hn.1
  · convert add_mem (show inH 40 by decide) hn.2 using 1 <;> omega

/-- Generator tests. Their equivalence with all positive H steps is proved below. -/
def socle (K : ℕ → Prop) (n : ℕ) : Prop :=
  inH n ∧ ¬K n ∧ K (n+8) ∧ K (n+13) ∧ K (n+15)
def source (K : ℕ → Prop) (n : ℕ) : Prop :=
  K n ∧ (8≤n → ¬K (n-8)) ∧ (13≤n → ¬K (n-13)) ∧ (15≤n → ¬K (n-15))

instance (K : ℕ → Prop) [DecidablePred K] (n : ℕ) : Decidable (socle K n) := inferInstanceAs (Decidable (_∧_))
instance (K : ℕ → Prop) [DecidablePred K] (n : ℕ) : Decidable (source K n) := inferInstanceAs (Decidable (_∧_))

 theorem positive_has_generator {d : ℕ} (hd : inH d) (hp : 0<d) :
    ∃ g∈({8,13,15}:Finset ℕ), ∃ r, inH r ∧ d=g+r := by
  obtain ⟨x,y,z,he⟩ := (membership_iff_coefficients d).mp hd
  by_cases hx : 0<x
  · exact ⟨8,by simp,8*(x-1)+13*y+15*z,coefficients_mem _ _ _,by omega⟩
  by_cases hy : 0<y
  · exact ⟨13,by simp,8*x+13*(y-1)+15*z,coefficients_mem _ _ _,by omega⟩
  have hz : 0<z := by omega
  exact ⟨15,by simp,8*x+13*y+15*(z-1),coefficients_mem _ _ _,by omega⟩

 theorem socle_iff_all_steps (K : ℕ → Prop)
    (hclosed : ∀ {n d}, K n → inH d → K (n+d)) (n : ℕ) :
    socle K n ↔ inH n ∧ ¬K n ∧ ∀ d, inH d → 0<d → K (n+d) := by
  constructor
  · rintro ⟨hn,hout,h8,h13,h15⟩
    refine ⟨hn,hout,?_⟩
    intro d hd hp
    obtain ⟨g,hg,r,hr,rfl⟩ := positive_has_generator hd hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · simpa [Nat.add_assoc] using hclosed h8 hr
    · simpa [Nat.add_assoc] using hclosed h13 hr
    · simpa [Nat.add_assoc] using hclosed h15 hr
  · rintro ⟨hn,hout,ha⟩
    exact ⟨hn,hout,ha 8 (by decide) (by decide),ha 13 (by decide) (by decide),ha 15 (by decide) (by decide)⟩

 theorem source_iff_no_divisor (K : ℕ → Prop)
    (hclosed : ∀ {n d}, K n → inH d → K (n+d)) (n : ℕ) :
    source K n ↔ K n ∧ ∀ v d, K v → inH d → 0<d → n≠v+d := by
  constructor
  · rintro ⟨hn,h8,h13,h15⟩
    refine ⟨hn,?_⟩
    intro v d hv hd hp he
    obtain ⟨g,hg,r,hr,hd⟩ := positive_has_generator hd hp
    have hvr := hclosed hv hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · exact h8 (by omega) (by convert hvr using 1 <;> omega)
    · exact h13 (by omega) (by convert hvr using 1 <;> omega)
    · exact h15 (by omega) (by convert hvr using 1 <;> omega)
  · rintro ⟨hn,ha⟩
    refine ⟨hn,?_,?_,?_⟩ <;> intro hle hv
    · exact ha (n-8) 8 hv (by decide) (by decide) (by omega)
    · exact ha (n-13) 13 hv (by decide) (by decide) (by omega)
    · exact ha (n-15) 15 hv (by decide) (by decide) (by omega)

 theorem old_socle_exact (n : ℕ) : socle oldIdeal n ↔ n=53 ∨ n=55 := by
  by_cases hn : n<56
  · interval_cases n <;> decide
  · have ht := old_tail n (by omega)
    simp only [socle]
    constructor
    · rintro ⟨_,hout,_⟩; exact (hout ht).elim
    · intro h; rcases h with rfl | rfl <;> omega

 theorem new_socle_exact (n : ℕ) : socle newIdeal n ↔ n=38 ∨ n=42 ∨ n=45 ∨ n=47 := by
  by_cases hn : n<56
  · interval_cases n <;> decide
  · have ht : newIdeal n := Or.inl (old_tail n (by omega))
    simp only [socle]
    constructor
    · rintro ⟨_,hout,_⟩; exact (hout ht).elim
    · intro h; rcases h with rfl | rfl | rfl | rfl <;> omega

 theorem old_sources_exact (n : ℕ) : source oldIdeal n ↔ n=28 ∨ n=46 ∨ n=48 ∨ n=50 := by
  by_cases hn : n<64
  · interval_cases n <;> decide
  · have ht := old_tail (n-8) (by omega)
    constructor
    · rintro ⟨_,h8,_⟩; exact (h8 (by omega) ht).elim
    · intro h; rcases h with rfl | rfl | rfl | rfl <;> omega

 theorem new_sources_exact (n : ℕ) : source newIdeal n ↔ n=28 ∨ n=40 ∨ n=46 ∨ n=50 := by
  by_cases hn : n<64
  · interval_cases n <;> decide
  · have ht : newIdeal (n-8) := Or.inl (old_tail (n-8) (by omega))
    constructor
    · rintro ⟨_,h8,_⟩; exact (h8 (by omega) ht).elim
    · intro h; rcases h with rfl | rfl | rfl | rfl <;> omega

 theorem erased_source_exact (n : ℕ) :
    source oldIdeal n ∧ (40≤n ∧ inH (n-40)) ↔ n=48 := by
  rw [old_sources_exact]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl,h⟩ <;> norm_num [inH,threshold] at *
  · rintro rfl; decide

 theorem finite_socle_counts :
    ((Finset.range 56).filter (socle oldIdeal)).card=2 ∧
    ((Finset.range 56).filter (socle newIdeal)).card=4 := by
  simp only [old_socle_exact,new_socle_exact]
  decide

 def oldSocleEquiv : {n // socle oldIdeal n} ≃ Fin 2 where
  toFun n := if n.val=53 then 0 else 1
  invFun i := if i=0 then ⟨53,by decide⟩ else ⟨55,by decide⟩
  left_inv n := by
    apply Subtype.ext
    rcases (old_socle_exact n.val).mp n.property with h | h <;> simp [h]
  right_inv i := by fin_cases i <;> decide

 def newSocleEquiv : {n // socle newIdeal n} ≃ Fin 4 where
  toFun n := if n.val=38 then 0 else if n.val=42 then 1 else if n.val=45 then 2 else 3
  invFun i := (![⟨38,by decide⟩,⟨42,by decide⟩,⟨45,by decide⟩,⟨47,by decide⟩] : Fin 4 → {n // socle newIdeal n}) i
  left_inv n := by
    apply Subtype.ext
    rcases (new_socle_exact n.val).mp n.property with h | h | h | h <;> simp [h]
  right_inv i := by fin_cases i <;> decide

 theorem actual_old_type : Nat.card {n // socle oldIdeal n}=2 := by
  rw [Nat.card_congr oldSocleEquiv]
  simp
 theorem actual_new_type : Nat.card {n // socle newIdeal n}=4 := by
  rw [Nat.card_congr newSocleEquiv]
  simp

 def erasedEquiv : {n // source oldIdeal n ∧ 40≤n ∧ inH (n-40)} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨48,by decide⟩
  left_inv n := Subtype.ext ((erased_source_exact n.val).mp n.property).symm
  right_inv u := by cases u; rfl
 theorem actual_erasure_count :
    Nat.card {n // source oldIdeal n ∧ 40≤n ∧ inH (n-40)}=1 := by
  rw [Nat.card_congr erasedEquiv]
  simp

/-- The actual finite-semigroup type difference violates 2-e. All three
cardinalities are attached to the proved global semigroup/ideal predicates. -/
 theorem actual_overstrong_bound_false :
    ¬ ((Nat.card {n // socle newIdeal n}:ℤ)-Nat.card {n // socle oldIdeal n} ≤
      2-Nat.card {n // source oldIdeal n ∧ 40≤n ∧ inH (n-40)}) := by
  rw [actual_old_type,actual_new_type,actual_erasure_count]
  decide

 theorem overstrong_bound_false : ¬ ((4:ℤ)-2≤2-1) := by decide

#print axioms membership_iff_coefficients
#print axioms old_socle_exact
#print axioms new_socle_exact
#print axioms source_iff_no_divisor
#print axioms erased_source_exact
#print axioms overstrong_bound_false
#print axioms actual_overstrong_bound_false
end NS25Lean.PrincipalTensorColonNegativeControl
