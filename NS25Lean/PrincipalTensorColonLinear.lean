import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
section TwoCochain
variable {k T : Type*} [Field k] [CommRing T] [Algebra k T]

/-- The two-variable Koszul COCHAIN maps, ordered Y,Z. -/
def twoKoszulD0 (y z : T) : T →ₗ[k] (Fin 2 → T) where
  toFun := fun t => ![y*t,z*t]
  map_add' := by intro a b; ext i; fin_cases i <;> simp [mul_add]
  map_smul' := by intro a b; ext i; fin_cases i <;> simp

def twoKoszulD1 (y z : T) : (Fin 2 → T) →ₗ[k] T where
  toFun := fun t => z*t 0-y*t 1
  map_add' := by intro a b; simp; ring
  map_smul' := by intro a b; simp [mul_smul_comm,smul_sub]

theorem twoKoszul_range_D0_le_cycles (y z : T) :
    LinearMap.range (twoKoszulD0 (k:=k) y z) ≤ LinearMap.ker (twoKoszulD1 y z) := by
  rintro _ ⟨t,rfl⟩
  change z*(y*t)-y*(z*t)=0
  ring

abbrev TwoKoszulH0 (y z : T) := LinearMap.ker (twoKoszulD0 (k:=k) y z)
abbrev TwoKoszulH1 (y z : T) :=
  LinearMap.ker (twoKoszulD1 (k:=k) y z) ⧸
    (LinearMap.range (twoKoszulD0 (k:=k) y z)).comap (LinearMap.ker (twoKoszulD1 y z)).subtype
abbrev TwoKoszulH2 (y z : T) := T ⧸ LinearMap.range (twoKoszulD1 (k:=k) y z)

/-- Rank-nullity, without truncated dimension subtraction. This generic Euler
identity is later instantiated on the actual staircase quotient. -/
theorem twoKoszul_finrank_euler [Module.Finite k T] (y z : T) :
    Module.finrank k (TwoKoszulH1 (k:=k) y z) =
      Module.finrank k (TwoKoszulH0 (k:=k) y z) +
      Module.finrank k (TwoKoszulH2 (k:=k) y z) := by
  have h0 := LinearMap.finrank_range_add_finrank_ker (twoKoszulD0 (k:=k) y z)
  have h1 := LinearMap.finrank_range_add_finrank_ker (twoKoszulD1 (k:=k) y z)
  have h2 := (LinearMap.range (twoKoszulD1 (k:=k) y z)).finrank_quotient_add_finrank
  have hh := ((LinearMap.range (twoKoszulD0 (k:=k) y z)).comap
    (LinearMap.ker (twoKoszulD1 (k:=k) y z)).subtype).finrank_quotient_add_finrank
  have hb := (Submodule.comapSubtypeEquivOfLe
    (twoKoszul_range_D0_le_cycles (k:=k) y z)).finrank_eq
  have hp : Module.finrank k (Fin 2 → T) = 2*Module.finrank k T := by
    simp [Module.finrank_pi_fintype]
  change Module.finrank k (TwoKoszulH1 (k:=k) y z) + _ = _ at hh
  change Module.finrank k (TwoKoszulH2 (k:=k) y z) + _ = _ at h2
  change _ + Module.finrank k (TwoKoszulH0 (k:=k) y z) = _ at h0
  omega
end TwoCochain

/-- The exact low cohomology segment retains the negative colon socle term.
The comparison need only be known to kill the connecting image. -/
theorem principal_finrank_balance_le
    {k U V W T Z : Type*} [Field k]
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [Module.Finite k T]
    [AddCommGroup Z] [Module k Z]
    (i : U →ₗ[k] V) (p : V →ₗ[k] W) (d : W →ₗ[k] T) (c : T →ₗ[k] Z)
    (hi : Function.Injective i) (hip : LinearMap.range i=LinearMap.ker p)
    (hpd : LinearMap.range p=LinearMap.ker d)
    (hdc : LinearMap.range d ≤ LinearMap.ker c) :
    Module.finrank k W + Module.finrank k U + Module.finrank k (LinearMap.range c) ≤
      Module.finrank k V + Module.finrank k T := by
  have hk : Module.finrank k (LinearMap.ker p)=Module.finrank k U := by
    rw [← hip,LinearMap.finrank_range_of_inj hi]
  have hp := LinearMap.finrank_range_add_finrank_ker p
  have hd := LinearMap.finrank_range_add_finrank_ker d
  have hc := LinearMap.finrank_range_add_finrank_ker c
  have hr := Submodule.finrank_mono hdc
  rw [hk] at hp
  rw [← hpd] at hd
  omega

/-- The balance above as an integer difference: the colon socle is subtracted. -/
theorem principal_finrank_delta_le
    {k U V W T Z : Type*} [Field k]
    [AddCommGroup U] [Module k U] [Module.Finite k U]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [Module.Finite k T]
    [AddCommGroup Z] [Module k Z]
    (i : U →ₗ[k] V) (p : V →ₗ[k] W) (d : W →ₗ[k] T) (c : T →ₗ[k] Z)
    (hi : Function.Injective i) (hip : LinearMap.range i=LinearMap.ker p)
    (hpd : LinearMap.range p=LinearMap.ker d)
    (hdc : LinearMap.range d ≤ LinearMap.ker c) :
    (Module.finrank k W : ℤ)-Module.finrank k V ≤
      -(Module.finrank k U : ℤ)+Module.finrank k T-Module.finrank k (LinearMap.range c) := by
  have h := principal_finrank_balance_le i p d c hi hip hpd hdc
  omega
end NS25Lean.L5A2BFinalRepair
