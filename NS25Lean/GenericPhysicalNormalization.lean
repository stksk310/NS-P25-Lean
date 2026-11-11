import NS25Lean.P2ReturnExchange
import NS25Lean.TailIdealNormalization

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericPhysical
open FourGeneratedBridge L5A2C4OR19 ReturnExchange
open scoped Classical

/-- A displayed numerical four-generator presentation. Minimality and
multiplicity are deliberately absent. -/
structure Presentation (H Gamma : NumericalSemigroup) where
  a : ℕ
  b : ℕ
  c : ℕ
  m : ℕ
  delta : ℕ
  a_pos : 0<a
  b_pos : 0<b
  c_pos : 0<c
  m_pos : 0<m
  delta_pos : 0<delta
  tail_generated : H.toAddSubmonoid=generatedThree a b c
  physical_generated : Gamma.toAddSubmonoid=
    generatedFour m (delta*a) (delta*b) (delta*c)

variable {H Gamma : NumericalSemigroup}

def Presentation.scaledTail (D : Presentation H Gamma) : AddSubmonoid ℕ :=
  generatedThree (D.delta*D.a) (D.delta*D.b) (D.delta*D.c)

theorem Presentation.scaled_mem (D : Presentation H Gamma) (w : ℕ) :
    w∈D.scaledTail ↔ ∃ x∈H, w=D.delta*x := by
  change w∈generatedThree (D.delta*D.a) (D.delta*D.b) (D.delta*D.c) ↔
    ∃ x∈H.toAddSubmonoid, w=D.delta*x
  rw [D.tail_generated]
  exact generatedThree_scale D.delta D.a D.b D.c w

theorem Presentation.scaled_mul_mem (D : Presentation H Gamma) (x : ℕ) :
    D.delta*x∈D.scaledTail ↔ x∈H := by
  rw [D.scaled_mem]
  constructor
  · rintro ⟨y,hy,he⟩
    have := Nat.eq_of_mul_eq_mul_left D.delta_pos he
    simpa [this] using hy
  · intro hx; exact ⟨x,hx,rfl⟩

theorem Presentation.generated_over (D : Presentation H Gamma) {w : ℕ}
    (hw : w∈Gamma) : ∃ s h : ℕ, h∈H ∧ w=s*D.m+D.delta*h := by
  have hw' : w∈generatedFour D.m (D.delta*D.a) (D.delta*D.b) (D.delta*D.c) := by
    change w∈Gamma.toAddSubmonoid at hw
    rwa [D.physical_generated] at hw
  obtain ⟨s,t,ht,he⟩ := generatedFour_isGeneratedOver _ _ _ _ w hw'
  obtain ⟨h,hh,hth⟩ := (D.scaled_mem t).mp ht
  exact ⟨s,h,hh,by omega⟩

theorem Presentation.scaled_inclusion (D : Presentation H Gamma) :
    D.scaledTail≤Gamma.toAddSubmonoid := by
  rw [D.physical_generated]
  exact generatedThree_le_generatedFour _ _ _ _

/-- Numericality forces coprimality without minimal-generator hypotheses. -/
theorem Presentation.coprime (D : Presentation H Gamma) : Nat.Coprime D.delta D.m := by
  let g := Nat.gcd D.delta D.m
  have gd : g∣D.delta := Nat.gcd_dvd_left _ _
  have gm : g∣D.m := Nat.gcd_dvd_right _ _
  have all (x : ℕ) (hx : x∈Gamma) : g∣x := by
    obtain ⟨s,h,hh,he⟩ := D.generated_over hx
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right gm s) (dvd_mul_of_dvd_left gd h)
  obtain ⟨N,hN⟩ := Gamma.exists_conductor
  have h0 := all N (hN N le_rfl)
  have h1 := all (N+1) (hN (N+1) (by omega))
  have hg : g∣1 := by simpa using Nat.dvd_sub h1 h0
  exact Nat.dvd_one.mp hg

def Presentation.physicalCut (D : Presentation H Gamma) : Set ℕ :=
  aperyTail Gamma.toAddSubmonoid D.scaledTail D.m

def Presentation.normalizedCut (D : Presentation H Gamma) : Set ℕ :=
  {x | x∈H ∧ D.m≤D.delta*x ∧ D.delta*x-D.m∈Gamma}

theorem Presentation.physicalCut_mul_iff (D : Presentation H Gamma) (x : ℕ) :
    D.delta*x∈D.physicalCut ↔ x∈D.normalizedCut := by
  exact and_congr (D.scaled_mul_mem x) Iff.rfl

/-- The true physical multiplier is delta*q, retaining the delta=q=1 endpoint. -/
theorem Presentation.normalizedCut_iff_returns (D : Presentation H Gamma) (x : ℕ) :
    x∈D.normalizedCut ↔ x∈cyclicCut H D.m := by
  constructor
  · rintro ⟨hx,hm,hphys⟩
    obtain ⟨s,h,hh,he⟩ := D.generated_over hphys
    have hmul : D.delta*x=(s+1)*D.m+D.delta*h := by
      rw [Nat.add_mul,one_mul]
      omega
    have hdiv : D.delta∣(s+1)*D.m := by
      have hd0 : D.delta∣D.delta*x := dvd_mul_right _ _
      have hd1 : D.delta∣D.delta*h := dvd_mul_right _ _
      have hd := Nat.dvd_sub hd0 hd1
      have he' : D.delta*x-D.delta*h=(s+1)*D.m := by omega
      simpa only [he'] using hd
    obtain ⟨q,hq⟩ := D.coprime.dvd_of_dvd_mul_right hdiv
    have hqpos : 0<q := by
      by_contra hn
      have hz : q=0 := by omega
      rw [hz,mul_zero] at hq
      omega
    refine ⟨hx,q,hqpos,h,hh,?_⟩
    apply Nat.eq_of_mul_eq_mul_left D.delta_pos
    nlinarith [hmul]
  · rintro ⟨hx,q,hq,h,hh,he⟩
    have hdp : 0<D.delta*q := Nat.mul_pos D.delta_pos hq
    have hpmem : D.m∈Gamma := by
      change D.m∈Gamma.toAddSubmonoid
      rw [D.physical_generated]
      exact firstGenerator_mem_generatedFour _ _ _ _
    have hhmem : D.delta*h∈Gamma := D.scaled_inclusion ((D.scaled_mul_mem h).mpr hh)
    have hs := Gamma.add_mem (Gamma.toAddSubmonoid.nsmul_mem hpmem (D.delta*q-1)) hhmem
    have hcoef : (D.delta*q-1)*D.m+D.m=(D.delta*q)*D.m := by
      have := congrArg (fun n => n*D.m) (Nat.sub_add_cancel (by omega : 1≤D.delta*q))
      simpa only [Nat.add_mul,one_mul] using this
    have hex : D.delta*x=(D.delta*q-1)*D.m+D.delta*h+D.m := by
      calc
        D.delta*x=D.delta*(q*D.m+h) := congrArg (fun t => D.delta*t) he
        _ = D.delta*q*D.m+D.delta*h := by ring
        _ = _ := by omega
    refine ⟨hx,by omega,?_⟩
    have heq : D.delta*x-D.m=(D.delta*q-1)*D.m+D.delta*h := by omega
    rw [heq]
    simpa [nsmul_eq_mul] using hs

theorem Presentation.zero_not_cut (D : Presentation H Gamma) : 0∉D.normalizedCut := by
  intro h
  have := h.2.1
  simp only [mul_zero] at this
  have := D.m_pos
  omega

theorem Presentation.cut_add (D : Presentation H Gamma) {x h : ℕ}
    (hx : x∈D.normalizedCut) (hh : h∈H) : x+h∈D.normalizedCut := by
  rw [D.normalizedCut_iff_returns] at hx ⊢
  obtain ⟨hx,q,hq,r,hr,he⟩ := hx
  exact ⟨H.add_mem hx hh,q,hq,r+h,H.add_mem hr hh,by omega⟩

theorem Presentation.cut_finite_reduction (D : Presentation H Gamma) (x : ℕ) :
    x∈D.normalizedCut ↔ x∈H ∧ ∃ q : ℕ, 0<q ∧
      q≤firstPrincipal H D.m D.m_pos ∧ ∃ h∈H, x=q*D.m+h := by
  rw [D.normalizedCut_iff_returns]
  exact cyclicCut_finite_principal_reduction H D.m D.m_pos x

theorem Presentation.principal_endpoint (D : Presentation H Gamma) (x : ℕ) :
    x∈H ∧ (∃ h∈H, x=firstPrincipal H D.m D.m_pos*D.m+h) ↔
      ∃ h∈H, x=firstPrincipal H D.m D.m_pos*D.m+h := by
  constructor
  · exact And.right
  · rintro ⟨h,hh,rfl⟩
    exact ⟨H.add_mem (firstPrincipal_spec H D.m D.m_pos).2 hh,h,hh,rfl⟩

theorem Presentation.before_principal_not_mem (D : Presentation H Gamma) {q : ℕ}
    (hq : 0<q) (hQ : q<firstPrincipal H D.m D.m_pos) : q*D.m∉H := by
  intro h
  have := firstPrincipal_le H D.m D.m_pos hq h
  omega

theorem Presentation.cut_nonempty (D : Presentation H Gamma) : D.normalizedCut.Nonempty := by
  rw [Set.Nonempty]
  refine ⟨firstPrincipal H D.m D.m_pos*D.m,?_⟩
  rw [D.normalizedCut_iff_returns]
  exact ⟨(firstPrincipal_spec H D.m D.m_pos).2,firstPrincipal H D.m D.m_pos,
    (firstPrincipal_spec H D.m D.m_pos).1,0,H.zero_mem,by simp⟩

/-- In fact the normalized cut is cofinite in all natural numbers. -/
theorem Presentation.cut_finite_complement (D : Presentation H Gamma) :
    Set.Finite {x : ℕ | x∉D.normalizedCut} := by
  obtain ⟨N,hN⟩ := H.exists_conductor
  let f := firstPrincipal H D.m D.m_pos*D.m
  apply (Set.finite_lt_nat (f+N)).subset
  intro x hx
  by_contra hn
  have hxge : f+N≤x := by simpa using hn
  have hr : x-f∈H := hN _ (by omega)
  have hf : f∈H := (firstPrincipal_spec H D.m D.m_pos).2
  apply hx
  rw [D.normalizedCut_iff_returns]
  exact ⟨by simpa only [Nat.add_sub_of_le (by omega : f≤x)] using H.add_mem hf hr,
    firstPrincipal H D.m D.m_pos,(firstPrincipal_spec H D.m D.m_pos).1,
    x-f,hr,by dsimp only [f] at *; omega⟩

/-- The existing full scaling interface is constructed without minimality. -/
def Presentation.scaling (D : Presentation H Gamma) :
    TailScaling Gamma.toAddSubmonoid D.scaledTail D.m where
  Hbar := H
  d := D.delta
  positive := D.delta_pos
  scale := D.scaled_mem
  inclusion := D.scaled_inclusion
  nonempty := by
    obtain ⟨x,hx⟩ := D.cut_nonempty
    exact ⟨D.delta*x,(D.physicalCut_mul_iff x).mpr hx⟩

theorem Presentation.scaling_ideal_nat (D : Presentation H Gamma) (x : ℕ) :
    (x : ℤ)∈D.scaling.ideal ↔ x∈D.normalizedCut :=
  (D.scaling.mem_ideal_nat x).trans (D.physicalCut_mul_iff x)

def Presentation.cutEquiv (D : Presentation H Gamma) :
    {x : ℕ // x∈D.normalizedCut} ≃ {w : ℕ // w∈D.physicalCut} :=
  Equiv.ofBijective (fun x => ⟨D.delta*x.val,(D.physicalCut_mul_iff x.val).mpr x.property⟩) (by
    constructor
    · intro x y he
      exact Subtype.ext (Nat.eq_of_mul_eq_mul_left D.delta_pos (congrArg Subtype.val he))
    · intro w
      obtain ⟨x,hx,he⟩ := (D.scaled_mem w.val).mp w.property.1
      refine ⟨⟨x,(D.physicalCut_mul_iff x).mp (he ▸ w.property)⟩,?_⟩
      exact Subtype.ext he.symm)

theorem Presentation.cutEquiv_value (D : Presentation H Gamma)
    (x : {x : ℕ // x∈D.normalizedCut}) : (D.cutEquiv x).val=D.delta*x.val := rfl

theorem Presentation.cutEquiv_order (D : Presentation H Gamma)
    (x y : {x : ℕ // x∈D.normalizedCut}) :
    (D.cutEquiv x).val≤(D.cutEquiv y).val ↔ x.val≤y.val := by
  change D.delta*x.val≤D.delta*y.val ↔ x.val≤y.val
  constructor
  · intro h
    nlinarith [D.delta_pos]
  · exact Nat.mul_le_mul_left D.delta

theorem Presentation.predecessor_iff (D : Presentation H Gamma) (x g : ℕ) :
    D.delta*x-D.delta*g∈D.physicalCut ↔ x-g∈D.normalizedCut := by
  rw [←Nat.mul_sub_left_distrib,D.physicalCut_mul_iff]

theorem Presentation.source_scaling (D : Presentation H Gamma) (x : ℕ) :
    IsMinimalTailGenerator D.scaledTail D.physicalCut (D.delta*x) ↔
      D.scaling.ideal.IsMinimalGenerator (x : ℤ) := D.scaling.generator_iff x

theorem Presentation.socle_scaling (D : Presentation H Gamma) (x : ℕ) :
    IsSocle Gamma.toAddSubmonoid D.scaledTail D.m (D.delta*x) ↔
      IsIntegralSocle D.scaling.ideal (x : ℤ) := D.scaling.socle_iff x

def vectorWeight (a b c : ℕ) (u : Fin 3→ℕ) : ℕ := u 0*a+u 1*b+u 2*c

theorem vectorWeight_scale (delta a b c : ℕ) (u : Fin 3→ℕ) :
    vectorWeight (delta*a) (delta*b) (delta*c) u=delta*vectorWeight a b c u := by
  unfold vectorWeight
  ring

/-- The full set of exponent vectors is unchanged, not a selected factorization. -/
theorem Presentation.factorization_vectors (D : Presentation H Gamma) (n : ℕ) :
    {u : Fin 3→ℕ | vectorWeight (D.delta*D.a) (D.delta*D.b) (D.delta*D.c) u=D.delta*n}=
      {u : Fin 3→ℕ | vectorWeight D.a D.b D.c u=n} := by
  ext u
  simp only [Set.mem_setOf_eq,vectorWeight_scale]
  exact ⟨Nat.eq_of_mul_eq_mul_left D.delta_pos,congrArg (fun t => D.delta*t)⟩

/-- Edges in the factorization graph are the same literal support-overlap test. -/
theorem Presentation.factorization_graph (D : Presentation H Gamma) (n : ℕ)
    (u v : Fin 3→ℕ) :
    (vectorWeight (D.delta*D.a) (D.delta*D.b) (D.delta*D.c) u=D.delta*n ∧
      vectorWeight (D.delta*D.a) (D.delta*D.b) (D.delta*D.c) v=D.delta*n ∧
      u≠v ∧ ∃ i, 0<u i ∧ 0<v i) ↔
    (vectorWeight D.a D.b D.c u=n ∧ vectorWeight D.a D.b D.c v=n ∧
      u≠v ∧ ∃ i, 0<u i ∧ 0<v i) := by
  have hu := Set.ext_iff.mp (D.factorization_vectors n) u
  have hv := Set.ext_iff.mp (D.factorization_vectors n) v
  exact and_congr hu (and_congr hv Iff.rfl)

end NS25Lean.GenericPhysical
