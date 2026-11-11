import NS25Lean.GenericPhysicalNormalization
import NS25Lean.P2BranchBHighAxisCUTargetExclusion

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open FourGeneratedBridge L5A2B4AR1 L5A2C4H L5A2C4OR3 L5A2C4OR19 ReturnExchange
open scoped Classical

/-- The actual all-positive-return union as an integer relative ideal. -/
def cutIdeal (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) : RelativeIdeal H where
  carrier := {z | ∃ x : ℕ, x∈cyclicCut H m ∧ z=x}
  nonempty := by
    let Q := firstPrincipal H m hm
    have hQ := firstPrincipal_spec H m hm
    exact ⟨Q*m,Q*m,⟨hQ.2,Q,hQ.1,0,H.zero_mem,by simp⟩,rfl⟩
  bddBelow := ⟨0,by rintro z ⟨x,hx,rfl⟩; exact Int.natCast_nonneg x⟩
  add_mem := by
    rintro z h ⟨x,hx,rfl⟩ hh
    obtain ⟨hx,q,hq,r,hr,he⟩ := hx
    exact ⟨x+h,⟨H.add_mem hx hh,q,hq,r+h,H.add_mem hr hh,by omega⟩,by simp⟩

theorem cutIdeal_nat (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) (x : ℕ) :
    (x : ℤ)∈cutIdeal H m hm ↔ x∈cyclicCut H m := by
  constructor
  · rintro ⟨y,hy,he⟩
    have : x=y := by exact_mod_cast he
    simpa [this] using hy
  · exact fun hx => ⟨x,hx,rfl⟩

/-- The first-principal endpoint is included in the finite union. -/
theorem cutIdeal_finite_union (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) (z : ℤ) :
    z∈cutIdeal H m hm ↔ ∃ q : ℕ, 0<q ∧ q≤firstPrincipal H m hm ∧
      z∈returnIdeal H (q*m) := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨hx,q,hq,hQ,h,hh,he⟩ := (cyclicCut_finite_principal_reduction H m hm x).mp hx
    refine ⟨q,hq,hQ,⟨x,hx,rfl⟩,h,hh,?_⟩
    rw [he]
    push_cast
    ring
  · rintro ⟨q,hq,hQ,⟨x,hx,he⟩,h,hh,hr⟩
    have hxret : x=q*m+h := by
      rw [he] at hr
      push_cast at hr
      exact_mod_cast (show (x : ℤ)=(q*m+h : ℕ) by push_cast; omega)
    exact ⟨x,⟨hx,q,hq,h,hh,hxret⟩,he⟩

theorem return_mem_cutIdeal (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    {q : ℕ} (hq : 0<q) {z : ℤ} (hz : z∈returnIdeal H (q*m)) :
    z∈cutIdeal H m hm := by
  obtain ⟨x,hx,he⟩ := hz.1
  obtain ⟨h,hh,hr⟩ := hz.2
  have hxret : x=q*m+h := by
    rw [he] at hr
    push_cast at hr
    exact_mod_cast (show (x : ℤ)=(q*m+h : ℕ) by push_cast; omega)
  exact ⟨x,⟨hx,q,hq,h,hh,hxret⟩,he⟩

theorem firstPrincipal_eq_one_iff (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) :
    firstPrincipal H m hm=1 ↔ m∈H := by
  constructor
  · intro he
    simpa [he] using (firstPrincipal_spec H m hm).2
  · intro h
    have hle := firstPrincipal_le H m hm (n:=1) (by omega) (by simpa using h)
    have hp := (firstPrincipal_spec H m hm).1
    omega

def residueCandidate (H : NumericalSemigroup) (m a : ℕ) [NeZero a]
    (r : ZMod a) (q : ℕ) : ℤ :=
  max (H.asRelativeIdeal.aperyRepresentative a r)
    ((q*m : ℕ)+H.asRelativeIdeal.aperyRepresentative a (r-(q*m : ℕ)))

theorem residueCandidate_eq_return (H : NumericalSemigroup) (m a : ℕ) [NeZero a]
    (ha : a∈H) (r : ZMod a) (q : ℕ) :
    residueCandidate H m a r q=(returnIdeal H (q*m)).aperyRepresentative a r :=
  (L5A2B4AR5B.returnIdeal_aperyRepresentative_eq_max H (q*m) a ha r).symm

def residueCandidates (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) (a : ℕ) [NeZero a]
    (r : ZMod a) : Finset ℤ :=
  (Finset.Icc 1 (firstPrincipal H m hm)).image (residueCandidate H m a r)

theorem residueCandidates_nonempty (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (a : ℕ) [NeZero a] (r : ZMod a) : (residueCandidates H m hm a r).Nonempty := by
  have hQ := (firstPrincipal_spec H m hm).1
  refine ⟨residueCandidate H m a r (firstPrincipal H m hm),?_⟩
  apply Finset.mem_image.mpr
  exact ⟨firstPrincipal H m hm,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,rfl⟩

/-- The finite max-min law is derived from actual least representatives. -/
theorem cut_apery_eq_finite_minimum (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (a : ℕ) [NeZero a] (ha : a∈H) (r : ZMod a) :
    (cutIdeal H m hm).aperyRepresentative a r=
      (residueCandidates H m hm a r).min' (residueCandidates_nonempty H m hm a r) := by
  let I := cutIdeal H m hm
  let lam := I.aperyRepresentative a r
  have hmod : (lam : ZMod a)=r := I.aperyRepresentative_mod a r
  have hmem : lam∈I := I.aperyRepresentative_mem a r
  have lower (q : ℕ) (hq : 0<q) : lam≤residueCandidate H m a r q := by
    rw [residueCandidate_eq_return H m a ha r q]
    apply I.aperyRepresentative_le a r
    · exact return_mem_cutIdeal H m hm hq ((returnIdeal H (q*m)).aperyRepresentative_mem a r)
    · exact (returnIdeal H (q*m)).aperyRepresentative_mod a r
  apply le_antisymm
  · apply Finset.le_min'
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    exact lower q (by have := (Finset.mem_Icc.mp hq).1; omega)
  · obtain ⟨q,hq,hQ,hr⟩ := (cutIdeal_finite_union H m hm lam).mp hmem
    have hrle := (returnIdeal H (q*m)).aperyRepresentative_le a r hr hmod
    rw [←residueCandidate_eq_return H m a ha r q] at hrle
    have hqc : residueCandidate H m a r q∈residueCandidates H m hm a r :=
      Finset.mem_image.mpr ⟨q,Finset.mem_Icc.mpr ⟨by omega,hQ⟩,rfl⟩
    exact (Finset.min'_le _ _ hqc).trans hrle

/-- The normalized height is nonnegative and integral, including Q=1. -/
theorem cut_apery_eq_alpha_add_height (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (a : ℕ) [NeZero a] (ha : a∈H) (r : ZMod a) :
    ∃ eta : ℕ, (cutIdeal H m hm).aperyRepresentative a r=
      H.asRelativeIdeal.aperyRepresentative a r+(a*eta : ℕ) := by
  let I := cutIdeal H m hm
  obtain ⟨x,hx,hxval⟩ := I.aperyRepresentative_mem a r
  have hH : I.aperyRepresentative a r∈H.asRelativeIdeal := ⟨x,hx.1,hxval⟩
  exact RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a
    (H.asRelativeIdeal.aperyRepresentative_le a r hH (I.aperyRepresentative_mod a r))
    ((I.aperyRepresentative_mod a r).trans (H.asRelativeIdeal.aperyRepresentative_mod a r).symm)

theorem physical_cutIdeal_eq {H Gamma : NumericalSemigroup}
    (D : GenericPhysical.Presentation H Gamma) : D.scaling.ideal=cutIdeal H D.m D.m_pos := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply (cutIdeal_nat H D.m D.m_pos x).mpr
    exact (D.normalizedCut_iff_returns x).mp ((D.physicalCut_mul_iff x).mp hx)
  · rintro ⟨x,hx,rfl⟩
    exact (D.scaling_ideal_nat x).mpr ((D.normalizedCut_iff_returns x).mpr hx)

end NS25Lean.GenericReturn
