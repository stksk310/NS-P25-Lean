import NS25Lean.P2SectorCPureBoundaryExceptionalCapR47
import NS25Lean.P2ReturnExchange

set_option autoImplicit false
set_option linter.style.header false
noncomputable section

namespace NS25Lean.CriticalReturnDuality
open ChosenBase FourGeneratedBridge L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A
  L5A2B4AR5A L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29
  L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 L5A2C4OR36 L5A2C4OR37
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR45 L5A2C4OR46 L5A2C4OR47
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The generic unique-fiber extraction is tied here to the original B,e cut.
No chart-normal uniqueness is substituted for full fiber uniqueness. -/
theorem actual_unique_cut_source_divisor (B : Data Gamma) (e : Fin 3≃Fin 3)
    (M : Monomial)
    (hK : monomialDegree B e M∈cyclicCut (routingH B e) (routingM B e))
    (hUF : ∀ z : Monomial, monomialDegree B e z=monomialDegree B e M → z=M) :
    ∃ s : ModelSources B e, ∃ z : Monomial,
      monomialDegree B e z=s.val ∧ Divides z M ∧
      (∀ w : Monomial, monomialDegree B e w=s.val → w=z) := by
  obtain ⟨s,d,hd,he⟩ := cut_source_cover B e _ hK
  obtain ⟨x,y,z,hs⟩ := L5A2C4OR6.routingH_factorization B e s.property.1.1
  obtain ⟨a,b,c,ht⟩ := L5A2C4OR6.routingH_factorization B e hd
  let u : Monomial := (x,y,z)
  let v : Monomial := (a,b,c)
  have hu : monomialDegree B e u=s.val := hs.symm
  have hv : monomialDegree B e v=d := ht.symm
  have huv : u+v=M := hUF _ (by rw [monomialDegree_add,hu,hv]; omega)
  refine ⟨s,u,hu,?_,?_⟩
  · have hx := congrArg (fun t : Monomial => t.1) huv
    have hy := congrArg (fun t : Monomial => t.2.1) huv
    have hz := congrArg (fun t : Monomial => t.2.2) huv
    exact ⟨by change x+a=M.1 at hx; change x≤M.1; omega,
      by change y+b=M.2.1 at hy; change y≤M.2.1; omega,
      by change z+c=M.2.2 at hz; change z≤M.2.2; omega⟩
  · intro w hw
    have hwv : w+v=M := hUF _ (by rw [monomialDegree_add,hw,hv]; omega)
    exact add_right_cancel (hwv.trans huv.symm)

/-- Reflection returns to the same physically scaled original cut. -/
theorem actual_scaled_live_reflection (B : Data Gamma) (e : Fin 3≃Fin 3)
    (n s r h g d t p : ℕ) (hn : 0<n)
    (hret : s=n*routingM B e+r) (hd : d∈routingH B e)
    (ht : t∈routingH B e) (hp : p∈routingH B e)
    (hdiv : h=s+d) (hrg : r=g+t) (hhg : h=g+p) : routingD B e*p∈B.K := by
  apply (actual_scaled_cut_iff B e p).mp
  exact ReturnExchange.guarded_live_reflection (routingH B e) (routingM B e)
    n s r h g d t p hn hret hd ht hp hdiv hrg hhg

/-- All nonfirst positive-Y wraps are in the ORIGINAL zero-Y ideal N. -/
theorem positive_nonfirst_wrap_in_original (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hnf : s≠firstSource R)
    (hy : 0<(sourceNormal R s).2.1) :
    OriginalZeroIdeal R ((sourceNormal R s).1+cr21 R.HD)
      ((sourceNormal R s).2.2+cr23 R.HD) := by
  have hnotfull : ¬FullySupported (sourceNormal R s) := by
    intro hf
    exact hnf (full_support_source_eq_first R s hf)
  by_cases hx : 0<(sourceNormal R s).1
  · have hz : (sourceNormal R s).2.2=0 := by
      by_contra hn
      exact hnotfull ⟨hx,hy,by omega⟩
    have hp := nonfirst_xy_strict_predecessor R s hnf hx hy
    exact originalZero_upward R hp le_rfl (by omega)
  · have hx0 : (sourceNormal R s).1=0 := by omega
    have hz : 0<(sourceNormal R s).2.2 := by
      by_contra hn
      apply source_not_divides_yC R s
      dsimp [Divides]
      have hb := (sourceNormal_spec R s).2.1
      exact ⟨by omega,by omega,by omega⟩
    have hp := nonfirst_yz_strict_predecessor R s hnf hy hz
    exact originalZero_upward R hp (by omega) le_rfl

/-- Derived actual cap data. The attainment assertions are conclusions. -/
theorem positive_actual_caps (R : ActualRolePacket P)
    (hn : c2 P.M.base R.e*routingB P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hy : 0<(sourceNormal R (firstSource R)).2.1)
    (hlive : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    cr21 R.HD<rightCap R hlive ∧ rightCap R hlive<c1 P.M.base R.e ∧
    cr23 R.HD<leftCap R hlive ∧ leftCap R hlive≤c3 P.M.base R.e ∧
    (∀ x z, x<rightCap R hlive → z<leftCap R hlive → ¬OriginalZeroIdeal R x z) ∧
    (∀ x z, cr21 R.HD≤x → cr23 R.HD≤z →
      (¬OriginalZeroIdeal R x z ↔ x<rightCap R hlive ∧ z<leftCap R hlive)) ∧
    (0<(sourceNormal R (firstSource R)).2.2 → ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).1=rightCap R hlive-cr21 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).2.2=0) ∧
    (0<(sourceNormal R (firstSource R)).1 → ∃ t : ModelSources P.M.base R.e,
      (sourceNormal R t).2.2=leftCap R hlive-cr23 R.HD ∧
      0<(sourceNormal R t).2.1 ∧ (sourceNormal R t).1=0) := by
  obtain ⟨h1,h2,h3,h4⟩ := centralCaps_bounds R hn hlive
  exact ⟨h1,h2,h3,h4,
    fun _ _ hx hz => originalZero_rectangle_empty R hn hy hlive hx hz,
    fun _ _ hx hz => originalZero_central_rectangle R hn hy hlive hx hz,
    actual_right_cap_forced R hn hy hlive,actual_left_cap_forced R hn hy hlive⟩

/-- The universal original packet statement keeps every actual branch. -/
theorem actual_packet_compensation (R : ActualRolePacket P) :
    survivingWrapCount R+
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
        Nat.card {z // z∈borderExceptional R} := actual_role_packet_compensation R

/-- The pure-pair adapter exchanges old Y,Z, since the internal relation
is old Z^d=X^rY^s. In common coordinates it is Y^d=X^rZ^s. -/
def swapYZ (g : Monomial) : Monomial := (g.1,g.2.2,g.2.1)

@[simp] theorem swapYZ_involutive (g : Monomial) : swapYZ (swapYZ g)=g := rfl

def swappedBoundaryOriginals (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  swapYZ '' boundaryOriginals A

theorem swapped_boundary_original_y_lt (A : SectorBCriticalRoleBranchA P)
    {g : Monomial} (hg : g∈swappedBoundaryOriginals A) : g.2.1<d A := by
  obtain ⟨w,hw,rfl⟩ := hg
  exact boundaryOriginals_z_lt A hw

theorem swapped_boundary_wrap (A : SectorBCriticalRoleBranchA P) (g : Monomial) :
    swapYZ (boundaryWrap A (swapYZ g))=(g.1+r A,0,g.2.2+s A) := rfl

/-- Pure-internal exchange supplies the transverse minimum in actual originals. -/
theorem actual_pure_internal_transverse_minimum (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    ∃ k : ℕ, 0<k ∧ (∃ t∈pureOriginals A, t.1=0 ∧ t.2.2=k) ∧
      ∀ t∈pureOriginals A, 0<t.2.2 → k≤t.2.2 :=
  least_z_zero_x_original G A ha hb

end NS25Lean.CriticalReturnDuality
