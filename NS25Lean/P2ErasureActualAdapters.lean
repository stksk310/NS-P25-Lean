import NS25Lean.P2ErasedSourceScreen
import NS25Lean.P2SectorCF2SourceFiberR30

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.ErasureActualAdapters
open ChosenBase L2B L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR5 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22 L5A2C4OR29
  ErasedSourceScreen FourGeneratedBridge L5A2B4AR1 ReturnExchange
variable {Gamma : NumericalSemigroup}

def actualTriple (B : Data Gamma) (e : Fin 3≃Fin 3) : Triple (routingH B e) where
  weight :=
    { toFun := fun u => u 0*routingA B e+u 1*routingB B e+u 2*routingC B e
      map_zero' := by simp
      map_add' := by intro u v; simp only [Finsupp.add_apply]; ring }
  positive := by
    intro i
    fin_cases i
    · simpa using routingA_pos B e
    · simpa using routingB_positive B e
    · simpa using routingC_positive B e
  member := by
    intro u
    exact (mem_generatedThree_iff _ _ _ _).mpr ⟨u 0,u 1,u 2,rfl⟩
  factor := by
    intro h hh
    obtain ⟨x,y,z,he⟩ := L5A2C4OR6.routingH_factorization B e hh
    refine ⟨Finsupp.single 0 x+Finsupp.single 1 y+Finsupp.single 2 z,?_⟩
    simpa using he.symm

@[simp] theorem actual_g_zero (B : Data Gamma) (e : Fin 3≃Fin 3) :
    (actualTriple B e).g 0=routingA B e := by simp [Triple.g,actualTriple]
@[simp] theorem actual_g_one (B : Data Gamma) (e : Fin 3≃Fin 3) :
    (actualTriple B e).g 1=routingB B e := by simp [Triple.g,actualTriple]
@[simp] theorem actual_g_two (B : Data Gamma) (e : Fin 3≃Fin 3) :
    (actualTriple B e).g 2=routingC B e := by simp [Triple.g,actualTriple]

theorem actual_generator_scale (B : Data Gamma) (e : Fin 3≃Fin 3) (i : Fin 3) :
    routingD B e*(actualTriple B e).g i=weights B (e i) := by
  fin_cases i
  · simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 1 0 0
  · simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 1 0
  · simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 0 1

theorem actual_weight_scale (B : Data Gamma) (e : Fin 3≃Fin 3) (u : Exponent) :
    routingD B e*(actualTriple B e).weight u=
      weight B (roleExponent e (u 0,u 1,u 2)) := by
  exact (roleExponent_weight B e (u 0,u 1,u 2)).symm

def actualCritical (B : Data Gamma) (e : Fin 3≃Fin 3) : Critical (actualTriple B e) where
  exponent := fun i => criticalExponent B (e i)
  positive := fun i => (criticalExponent_spec B (e i)).1
  outside := by
    intro i
    let v := herzogWitness B e i
    let u : Exponent := Finsupp.single 0 (v (e 0))+Finsupp.single 1 (v (e 1))+
      Finsupp.single 2 (v (e 2))
    have hu (j : Fin 3) : u j=v (e j) := by fin_cases j <;> simp [u]
    have hrole : roleExponent e (u 0,u 1,u 2)=v := by
      ext j
      obtain ⟨j,rfl⟩ := e.surjective j
      fin_cases j <;> simp [roleExponent,hu]
    refine ⟨u,by rw [hu]; exact herzogWitness_zero B e i,?_⟩
    have hs := actual_weight_scale B e u
    rw [hrole] at hs
    have hw := herzogWitness_weight B e i
    have hg := actual_generator_scale B e i
    have hd : 0<routingD B e := tailGcd_pos (weights_positive B (e 0))
    apply Nat.eq_of_mul_eq_mul_left hd
    change routingD B e*(actualTriple B e).weight u=
      routingD B e*(criticalExponent B (e i)*(actualTriple B e).g i)
    change weight B v=criticalExponent B (e i)*weights B (e i) at hw
    nlinarith only [hs,hw,hg]
  least := by
    intro i n u hn hui he
    apply criticalExponent_min B (e i) n
    refine ⟨hn,roleExponent e (u 0,u 1,u 2),?_,?_⟩
    · fin_cases i <;> simpa [roleExponent] using hui
    · have hs := actual_weight_scale B e u
      have hg := actual_generator_scale B e i
      nlinarith only [hs,hg,he]

def actualPositivePresentation (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) : PositivePresentation (actualCritical B e) where
  P := cr12 HD
  Q := cr13 HD
  U := cr21 HD
  V := cr23 HD
  W := cr31 HD
  Z := cr32 HD
  positive := coherent_coefficients_positive B e HD
  relationA := by simpa [actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations B e HD).1
  relationB := by simpa [actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations B e HD).2.1
  relationC := by simpa [actualCritical,L5A2C4A.herzogC] using (coherent_normalized_relations B e HD).2.2
  coherentB := (coherent_coefficients B e HD).2.1
  coherentC := (coherent_coefficients B e HD).2.2

def gapIndices (Q : ℕ) : Set ℕ := {n | 0<n ∧ n<Q}

theorem nat_prefix_iff (H : NumericalSemigroup) (m Q x : ℕ) :
    (x:ℤ)∈prefixCarrier H m Q ↔ x∈returnCut H m (gapIndices Q) := by
  constructor
  · rintro ⟨n,hn,hnQ,hx,hr⟩
    obtain ⟨x',hx',heX⟩ := hx
    obtain ⟨r,hr,heR⟩ := hr
    have hxx : x'=x := by exact_mod_cast heX.symm
    subst x'
    refine ⟨hx',n,⟨hn,hnQ⟩,hn,r,hr,?_⟩
    exact_mod_cast (show (x:ℤ)=(n*m:ℕ)+(r:ℤ) by omega)
  · rintro ⟨hx,n,⟨hn,hnQ⟩,_,r,hr,he⟩
    exact ⟨n,hn,hnQ,⟨x,hx,rfl⟩,r,hr,by rw [he]; push_cast; ring⟩

def prefixSourceToNat (H : NumericalSemigroup) (m Q : ℕ)
    (s : {s : ℤ // IsSource H (prefixCarrier H m Q) s}) :
    Sources H m (gapIndices Q) := by
  have hnon : 0≤s.val := by
    obtain ⟨_,_,_,⟨⟨x,_,hx⟩,_⟩⟩ := s.property.1
    rw [hx]; positivity
  have hcast : (s.val.toNat:ℤ)=s.val := Int.toNat_of_nonneg hnon
  refine ⟨s.val.toNat,(minimal_iff_literal H _ _).mpr ⟨?_,?_⟩⟩
  · exact (nat_prefix_iff H m Q _).mp (hcast.symm ▸ s.property.1)
  · intro y d hy hd he
    by_contra hn
    apply s.property.2 d hd hn
    have hy' := (nat_prefix_iff H m Q y).mpr hy
    have he' : (s.val.toNat:ℤ)=(y:ℤ)+(d:ℤ) := by exact_mod_cast he
    convert hy' using 1 <;> omega

theorem prefixSourceToNat_cast (H : NumericalSemigroup) (m Q : ℕ)
    (s : {s : ℤ // IsSource H (prefixCarrier H m Q) s}) :
    ((prefixSourceToNat H m Q s).val:ℤ)=s.val := by
  change (s.val.toNat:ℤ)=s.val
  apply Int.toNat_of_nonneg
  obtain ⟨_,_,_,⟨⟨x,_,hx⟩,_⟩⟩ := s.property.1
  rw [hx]; positivity

theorem prefix_erasure_to_nat (H : NumericalSemigroup) (m Q : ℕ)
    (s : {s : ℤ // IsSource H (prefixCarrier H m Q) s})
    (hs : s.val-(Q*m:ℕ)∈H.asRelativeIdeal) :
    Erased m Q (prefixSourceToNat H m Q s) := by
  obtain ⟨d,hd,he⟩ := hs
  refine ⟨d,hd,?_⟩
  have hc := prefixSourceToNat_cast H m Q s
  exact_mod_cast (show ((prefixSourceToNat H m Q s).val:ℤ)=(Q*m:ℕ)+(d:ℤ) by omega)

theorem firstPrincipal_eq_principalIndex (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) :
    firstPrincipal H m hm=principalIndex H m hm := by
  exact Nat.le_antisymm
    (firstPrincipal_le H m hm (principalIndex_spec H m hm).1 (principalIndex_spec H m hm).2)
    (principalIndex_min H m hm (firstPrincipal_spec H m hm).1 (firstPrincipal_spec H m hm).2)

end NS25Lean.ErasureActualAdapters
