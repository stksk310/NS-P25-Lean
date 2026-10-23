import NS25Lean.P2SectorCUniversalLegalDischargeR17

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR19

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4C L5A2C4D L5A2C4F L5A2C4G
  L5A2C4OR15

variable {Gamma : NumericalSemigroup}

/-- Provenance exported by the frozen nonsymmetric gate. No numerical gate,
count, discharge, or terminal conclusion is stored here. -/
structure ActualRolePacket (P : P2Data Gamma) where
  G : SectorCActualFibers P
  boundaryPure : boundaryComponents G
  boundaryMixed : boundaryComponents G
  internalPure : internalComponents G
  internalMixed : internalComponents G
  e : Fin 3 ≃ Fin 3
  HD : CoherentHerzogData P.M.base e
  boundary_ne : boundaryPure ≠ boundaryMixed
  internal_ne : internalPure ≠ internalMixed
  pureC : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2}
  mixedAB : componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1}
  pureB : componentSupport P.M.base G.internalDegree internalPure = {e 1}
  mixedAC : componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2}
  inactive : LocalSignature P.M (c1 P.M.base e * weights P.M.base (e 0)) 2 2

/-- G2, with actual support witnesses. The numerical conclusion is derived
from the zero killed-count, not included among the inputs. -/
theorem normalized_internal_pure_b_eta_pos {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (internalPure : internalComponents G) (boundaryPure : boundaryComponents G)
    (hpureB : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hpureC : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2}) :
    0 < eta P.M.base e (c2 P.M.base e - 1) 0 := by
  have hdegree := (actual_internal_boundary_critical_degrees G e internalPure
    boundaryPure hpureB hpureC).1
  by_contra hn
  have hz : eta P.M.base e (c2 P.M.base e - 1) 0 = 0 := by omega
  have hK := (eta_eq_zero_iff P.M.base e (c2 P.M.base e - 1) 0).mp hz
  have hsub : G.internalDegree - weights P.M.base (e 1) =
      gridDegree P.M.base e 0 (c2 P.M.base e - 1) 0 := by
    rw [hdegree]
    simp [gridDegree, Nat.sub_mul]
  have he1 : e 1 ∈ componentSupport P.M.base G.internalDegree internalPure := by
    rw [hpureB]
    simp
  obtain ⟨u, huC, hu1⟩ :=
    (mem_componentSupport P.M.base G.internalDegree internalPure (e 1)).mp he1
  have hkilled : BoundaryKilled P.M G.internalDegree internalPure :=
    ⟨u, huC, e 1, hu1, hsub.symm ▸ hK⟩
  have hpos : 0 < killedCount P.M G.internalDegree :=
    Nat.card_pos_iff.mpr ⟨⟨⟨internalPure, hkilled⟩⟩, inferInstance⟩
  have hzero := G.internalSignature.2
  omega

/-- The accepted numerical interface, used as a derived conclusion for the
actual branch and available as explicit premises only in abstract counting. -/
def MixedGateConditions (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Prop :=
  H0 B e < c1 B e ∧
    eta B e (cr12 HD) (cr13 HD - 1) = 0 ∧
    0 < eta B e (c2 B e - 1) 0 ∧
    0 < eta B e 0 (c3 B e - 1) ∧
    (eta B e (cr32 HD) 0 < cr31 HD ∨
      eta B e (cr32 HD - 1) 0 ≤ cr31 HD)

/-- G0–G4 on one and the same actual support-normalized packet. -/
theorem normalized_mixed_notch_G0_G4 {P : P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : SurvivingNotch P.M.base R.e R.HD) :
    MixedGateConditions P.M.base R.e R.HD := by
  obtain ⟨_, hQ, hH⟩ := actual_cm_gate R.G R.boundaryPure R.boundaryMixed
    R.e R.HD R.inactive hMixed hNotch
  have hG2 := normalized_internal_pure_b_eta_pos R.G R.e R.internalPure
    R.boundaryPure R.pureB R.pureC
  have hnum := mixed_orientation_numerical R.G R.e R.boundaryPure
    R.boundaryMixed R.pureC R.mixedAB R.HD hMixed
  refine ⟨hH, hQ, hG2, ?_, ?_⟩
  · change 0 < coherentY3 P.M.base R.e R.HD
    omega
  · change coherentZ3 P.M.base R.e R.HD < cr31 R.HD ∨
      coherentZ3minus P.M.base R.e R.HD ≤ cr31 R.HD
    rcases hnum.2 with hZ | hZm
    · exact Or.inl hZ
    · exact Or.inr (by omega)

/-- The actual dispatcher recovers all role proofs from the frozen C4G
existential. Only the mixed surviving-notch path carries G0–G4. -/
theorem actual_role_gate_dispatcher (P : P2Data Gamma)
    (hNS : NonsymmetricSectorC P) :
    ∃ R : ActualRolePacket P,
      DirectPFBranch P.M.base R.e R.HD ∨
        (SurvivingNotch P.M.base R.e R.HD ∧
          PureOrientation R.G R.boundaryPure R.boundaryMixed) ∨
        (SurvivingNotch P.M.base R.e R.HD ∧
          MixedOrientation R.G R.boundaryPure R.boundaryMixed ∧
          MixedGateConditions P.M.base R.e R.HD) := by
  obtain ⟨G, bp, bm, ip, im, e, HD, hbne, hine, hbc, hmab, hib, hmac,
    hinactive, horient, hgate, _hpure, _hwidth, _hmixed⟩ :=
    actual_nonsymmetric_gate_interface P hNS
  let R : ActualRolePacket P :=
    ⟨G, bp, bm, ip, im, e, HD, hbne, hine, hbc, hmab, hib, hmac, hinactive⟩
  refine ⟨R, ?_⟩
  rcases hgate with hDirect | hNotch
  · exact Or.inl hDirect
  · rcases horient with hPure | hMixed
    · exact Or.inr (Or.inl ⟨hNotch, hPure⟩)
    · exact Or.inr (Or.inr ⟨hNotch, hMixed,
        normalized_mixed_notch_G0_G4 R hMixed hNotch⟩)

end NS25Lean.L5A2C4OR19
