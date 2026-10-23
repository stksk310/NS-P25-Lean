import NS25Lean.P2SectorCSeedTargetShadowRepairR13

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR14

open L5A2C4H L5A2C4D L5A2C4OR3 L5A2C4OR5 L5A2C4OR13

variable {Gamma : NumericalSemigroup}
variable {B : ChosenBase.Data Gamma} {e : Fin 3 ≃ Fin 3}
variable {HD : CoherentHerzogData B e} {i j : ℕ}

/-- A canonicalized forward `b/c` square.  The three lifts are total
normalized-tail Apéry lifts.  They are not the cut-dependent `gridLift`. -/
structure CanonicalForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ) where
  eI : ℕ
  eJ : ℕ
  nI : ℕ
  nJ : ℕ
  qI : ℕ
  qJ : ℕ
  eLift : ℕ
  nLift : ℕ
  qLift : ℕ
  eDomain : HerzogLShapeDomain HD eI eJ
  nDomain : HerzogLShapeDomain HD nI nJ
  qDomain : HerzogLShapeDomain HD qI qJ
  eValue : normalizedGrid B e 0 i j + routingB B e =
    normalizedGrid B e eLift eI eJ
  nValue : normalizedGrid B e 0 i j + routingC B e =
    normalizedGrid B e nLift nI nJ
  qValue : normalizedGrid B e 0 i j + routingB B e + routingC B e =
    normalizedGrid B e qLift qI qJ

namespace CanonicalForwardPacket

theorem eResidue (P : CanonicalForwardPacket B e HD i j) :
    gridResidue B e P.eI P.eJ = gridResidue B e i j + routingB B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) P.eValue
  simpa only [Nat.cast_add, normalizedGrid_mod] using h.symm

theorem nResidue (P : CanonicalForwardPacket B e HD i j) :
    gridResidue B e P.nI P.nJ = gridResidue B e i j + routingC B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) P.nValue
  simpa only [Nat.cast_add, normalizedGrid_mod] using h.symm

theorem qResidue (P : CanonicalForwardPacket B e HD i j) :
    gridResidue B e P.qI P.qJ =
      gridResidue B e i j + routingB B e + routingC B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) P.qValue
  simpa only [Nat.cast_add, normalizedGrid_mod] using h.symm

theorem eAlpha (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    physicalAlpha B e (gridResidue B e i j) + routingB B e =
      physicalAlpha B e (gridResidue B e P.eI P.eJ) +
        (routingA B e : ℤ) * P.eLift := by
  have hb := L5A2C4OR6.herzogLShapeCanonicality B e HD i j hbase
  have he := L5A2C4OR6.herzogLShapeCanonicality B e HD P.eI P.eJ P.eDomain
  change (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) at hb
  change (normalizedGrid B e 0 P.eI P.eJ : ℤ) =
      physicalAlpha B e (gridResidue B e P.eI P.eJ) at he
  have hv : (normalizedGrid B e 0 i j : ℤ) + routingB B e =
      normalizedGrid B e P.eLift P.eI P.eJ := by exact_mod_cast P.eValue
  rw [hb] at hv
  have hsplit : (normalizedGrid B e P.eLift P.eI P.eJ : ℤ) =
      (routingA B e : ℤ) * P.eLift + normalizedGrid B e 0 P.eI P.eJ := by
    simp [normalizedGrid]
    ring
  rw [hsplit, he] at hv
  nlinarith

theorem nAlpha (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    physicalAlpha B e (gridResidue B e i j) + routingC B e =
      physicalAlpha B e (gridResidue B e P.nI P.nJ) +
        (routingA B e : ℤ) * P.nLift := by
  have hb := L5A2C4OR6.herzogLShapeCanonicality B e HD i j hbase
  have hn := L5A2C4OR6.herzogLShapeCanonicality B e HD P.nI P.nJ P.nDomain
  change (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) at hb
  change (normalizedGrid B e 0 P.nI P.nJ : ℤ) =
      physicalAlpha B e (gridResidue B e P.nI P.nJ) at hn
  have hv : (normalizedGrid B e 0 i j : ℤ) + routingC B e =
      normalizedGrid B e P.nLift P.nI P.nJ := by exact_mod_cast P.nValue
  rw [hb] at hv
  have hsplit : (normalizedGrid B e P.nLift P.nI P.nJ : ℤ) =
      (routingA B e : ℤ) * P.nLift + normalizedGrid B e 0 P.nI P.nJ := by
    simp [normalizedGrid]
    ring
  rw [hsplit, hn] at hv
  nlinarith

theorem qAlpha (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    physicalAlpha B e (gridResidue B e i j) + routingB B e + routingC B e =
      physicalAlpha B e (gridResidue B e P.qI P.qJ) +
        (routingA B e : ℤ) * P.qLift := by
  have hb := L5A2C4OR6.herzogLShapeCanonicality B e HD i j hbase
  have hq := L5A2C4OR6.herzogLShapeCanonicality B e HD P.qI P.qJ P.qDomain
  change (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) at hb
  change (normalizedGrid B e 0 P.qI P.qJ : ℤ) =
      physicalAlpha B e (gridResidue B e P.qI P.qJ) at hq
  have hv : (normalizedGrid B e 0 i j : ℤ) + routingB B e + routingC B e =
      normalizedGrid B e P.qLift P.qI P.qJ := by exact_mod_cast P.qValue
  rw [hb] at hv
  have hsplit : (normalizedGrid B e P.qLift P.qI P.qJ : ℤ) =
      (routingA B e : ℤ) * P.qLift + normalizedGrid B e 0 P.qI P.qJ := by
    simp [normalizedGrid]
    ring
  rw [hsplit, hq] at hv
  nlinarith

end CanonicalForwardPacket

/-- Ordinary row of the canonical forward packet. -/
def ordinaryForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .ordinary i j) :
    CanonicalForwardPacket B e HD i j where
  eI := i + 1
  eJ := j
  nI := i
  nJ := j + 1
  qI := i + 1
  qJ := j + 1
  eLift := 0
  nLift := 0
  qLift := 0
  eDomain := by
    change HerzogLShapeDomain HD (i + 1) (j + 1) at hk
    unfold HerzogLShapeDomain at hk ⊢
    omega
  nDomain := by
    change HerzogLShapeDomain HD (i + 1) (j + 1) at hk
    unfold HerzogLShapeDomain at hk ⊢
    omega
  qDomain := hk
  eValue := by simp [normalizedGrid]; ring
  nValue := by simp [normalizedGrid]; ring
  qValue := by simp [normalizedGrid]; ring

/-- Center row: the diagonal step is the `c₁` wrap. -/
def centerForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .center i j) :
    CanonicalForwardPacket B e HD i j where
  eI := cr12 HD
  eJ := cr13 HD - 1
  nI := cr12 HD - 1
  nJ := cr13 HD
  qI := 0
  qJ := 0
  eLift := 0
  nLift := 0
  qLift := L5A2C4A.c1 B e
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = cr12 HD ∧ j + 1 = cr13 HD at hk
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = cr12 HD ∧ j + 1 = cr13 HD at hk
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  eValue := by
    change i + 1 = cr12 HD ∧ j + 1 = cr13 HD at hk
    rw [← hk.1, ← hk.2]
    simp [normalizedGrid]
    ring
  nValue := by
    change i + 1 = cr12 HD ∧ j + 1 = cr13 HD at hk
    rw [← hk.1, ← hk.2]
    simp [normalizedGrid]
    ring
  qValue := by
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = cr12 HD ∧ j + 1 = cr13 HD at hk
    rw [← hk.1, ← hk.2] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega

/-- Upper-arm row: the east and diagonal steps use the `c₁` wrap. -/
def upperArmForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .upperArmInterior i j) :
    CanonicalForwardPacket B e HD i j where
  eI := 0
  eJ := j - cr13 HD
  nI := cr12 HD - 1
  nJ := j + 1
  qI := 0
  qJ := j + 1 - cr13 HD
  eLift := L5A2C4A.c1 B e
  nLift := 0
  qLift := L5A2C4A.c1 B e
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    unfold HerzogLShapeDomain
    omega
  eValue := by
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    have hj : cr13 HD + (j - cr13 HD) = j := Nat.add_sub_of_le hk.2.1
    rw [← hk.1] at hr
    have hjc := congrArg (fun n => n * routingC B e) hj
    simp [normalizedGrid, Nat.add_mul] at hr hjc ⊢
    omega
  nValue := by
    have hp := (coherent_coefficients_positive B e HD).1
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    rw [← hk.1]
    simp [normalizedGrid]
    ring
  qValue := by
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
    have hj : cr13 HD + (j + 1 - cr13 HD) = j + 1 := Nat.add_sub_of_le (by omega)
    rw [← hk.1] at hr
    have hjc := congrArg (fun n => n * routingC B e) hj
    simp [normalizedGrid, Nat.add_mul] at hr hjc ⊢
    omega

/-- Upper-right row: the east and diagonal steps use the `r₂₁` wrap. -/
def upperRightForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .upperRight i j) :
    CanonicalForwardPacket B e HD i j where
  eI := 0
  eJ := j + cr23 HD
  nI := L5A2C4A.c2 B e - 1
  nJ := j + 1
  qI := 0
  qJ := j + cr23 HD + 1
  eLift := cr21 HD
  nLift := 0
  qLift := cr21 HD
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    unfold HerzogLShapeDomain
    omega
  eValue := by
    have hr := (coherent_normalized_relations B e HD).2.1
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    rw [← hk.1] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  nValue := by
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    rw [← hk.1]
    simp [normalizedGrid]
    ring
  qValue := by
    have hr := (coherent_normalized_relations B e HD).2.1
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
    rw [← hk.1] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega

/-- Bottom-top row: the north and diagonal steps use the `r₃₁` wrap. -/
def bottomTopForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .bottomTop i j) :
    CanonicalForwardPacket B e HD i j where
  eI := i + 1
  eJ := L5A2C4A.c3 B e - 1
  nI := i + cr32 HD
  nJ := 0
  qI := i + cr32 HD + 1
  qJ := 0
  eLift := 0
  nLift := cr31 HD
  qLift := cr31 HD
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    unfold HerzogLShapeDomain
    omega
  eValue := by
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    rw [← hk.1]
    simp [normalizedGrid]
    ring
  nValue := by
    have hr := (coherent_normalized_relations B e HD).2.2
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    rw [← hk.1] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  qValue := by
    have hr := (coherent_normalized_relations B e HD).2.2
    change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
    rw [← hk.1] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega

/-- Bottom-notch row: the north and diagonal steps use the `c₁` wrap. -/
def bottomNotchForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .bottomNotchInterior i j) :
    CanonicalForwardPacket B e HD i j where
  eI := i + 1
  eJ := cr13 HD - 1
  nI := i - cr12 HD
  nJ := 0
  qI := i + 1 - cr12 HD
  qJ := 0
  eLift := 0
  nLift := L5A2C4A.c1 B e
  qLift := L5A2C4A.c1 B e
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    unfold HerzogLShapeDomain
    omega
  eValue := by
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    rw [← hk.1]
    simp [normalizedGrid]
    ring
  nValue := by
    have hr := (coherent_normalized_relations B e HD).1
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    have hi : cr12 HD + (i - cr12 HD) = i := Nat.add_sub_of_le hk.2.1
    rw [← hk.1] at hr
    have hib := congrArg (fun n => n * routingB B e) hi
    simp [normalizedGrid, Nat.add_mul] at hr hib ⊢
    omega
  qValue := by
    have hr := (coherent_normalized_relations B e HD).1
    change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
    have hi : cr12 HD + (i + 1 - cr12 HD) = i + 1 := Nat.add_sub_of_le (by omega)
    rw [← hk.1] at hr
    have hib := congrArg (fun n => n * routingB B e) hi
    simp [normalizedGrid, Nat.add_mul] at hr hib ⊢
    omega

/-- `κ₁` row, including both interacting wraps. -/
def kappa1ForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .kappa1 i j) :
    CanonicalForwardPacket B e HD i j where
  eI := 0
  eJ := L5A2C4A.c3 B e - 1
  nI := cr32 HD - 1
  nJ := 0
  qI := cr32 HD
  qJ := 0
  eLift := cr21 HD
  nLift := L5A2C4A.c1 B e
  qLift := L5A2C4A.c1 B e
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  eValue := by
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).2.1
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 = cr13 HD at hk
    have hJ : L5A2C4A.c3 B e - 1 = j + cr23 HD := by omega
    rw [← hk.1] at hr
    rw [hJ]
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  nValue := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 = cr13 HD at hk
    have hi : i = cr12 HD + (cr32 HD - 1) := by omega
    rw [hi]
    rw [← hk.2] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  qValue := by
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = L5A2C4A.c2 B e ∧ j + 1 = cr13 HD at hk
    have hi : i + 1 = cr12 HD + cr32 HD := by omega
    rw [← hk.2] at hr
    have hib := congrArg (fun n => n * routingB B e) hi
    simp [normalizedGrid, Nat.add_mul] at hr hib ⊢
    omega

/-- `κ₂` row, including both interacting wraps. -/
def kappa2ForwardPacket
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ)
    (hk : CanonicalLocation.Holds HD .kappa2 i j) :
    CanonicalForwardPacket B e HD i j where
  eI := 0
  eJ := cr23 HD - 1
  nI := L5A2C4A.c2 B e - 1
  nJ := 0
  qI := 0
  qJ := cr23 HD
  eLift := L5A2C4A.c1 B e
  nLift := cr31 HD
  qLift := L5A2C4A.c1 B e
  eDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  nDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  qDomain := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    unfold HerzogLShapeDomain
    omega
  eValue := by
    have hp := coherent_coefficients_positive B e HD
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = cr12 HD ∧ j + 1 = L5A2C4A.c3 B e at hk
    have hj : j = cr13 HD + (cr23 HD - 1) := by omega
    rw [hj]
    rw [← hk.1] at hr
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  nValue := by
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).2.2
    change i + 1 = cr12 HD ∧ j + 1 = L5A2C4A.c3 B e at hk
    have hI : L5A2C4A.c2 B e - 1 = i + cr32 HD := by omega
    rw [← hk.2] at hr
    rw [hI]
    simp [normalizedGrid, Nat.add_mul] at hr ⊢
    omega
  qValue := by
    have hs := coherent_coefficients B e HD
    have hr := (coherent_normalized_relations B e HD).1
    change i + 1 = cr12 HD ∧ j + 1 = L5A2C4A.c3 B e at hk
    have hj : j + 1 = cr13 HD + cr23 HD := by omega
    rw [← hk.1] at hr
    have hjc := congrArg (fun n => n * routingC B e) hj
    simp [normalizedGrid, Nat.add_mul] at hr hjc ⊢
    omega

/-- R14 exact target: every canonical cell has a fully canonicalized forward
packet, including all four boundary wraps and both `κ` corners. -/
theorem canonicalForwardPacket_exists
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j) :
    Nonempty (CanonicalForwardPacket B e HD i j) := by
  obtain ⟨k, hk⟩ := canonicalLocation_exists B e HD hij
  cases k with
  | ordinary => exact ⟨ordinaryForwardPacket B e HD i j hk⟩
  | center => exact ⟨centerForwardPacket B e HD i j hk⟩
  | upperArmInterior => exact ⟨upperArmForwardPacket B e HD i j hk⟩
  | upperRight => exact ⟨upperRightForwardPacket B e HD i j hk⟩
  | bottomTop => exact ⟨bottomTopForwardPacket B e HD i j hk⟩
  | bottomNotchInterior => exact ⟨bottomNotchForwardPacket B e HD i j hk⟩
  | kappa1 => exact ⟨kappa1ForwardPacket B e HD i j hk⟩
  | kappa2 => exact ⟨kappa2ForwardPacket B e HD i j hk⟩

/-- Canonical inverse `b` predecessor of a canonical target. -/
structure CanonicalPredecessorB
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ) where
  predI : ℕ
  predJ : ℕ
  predLift : ℕ
  predDomain : HerzogLShapeDomain HD predI predJ
  value : normalizedGrid B e 0 predI predJ + routingB B e =
    normalizedGrid B e predLift i j

/-- Canonical inverse `c` predecessor of a canonical target. -/
structure CanonicalPredecessorC
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ) where
  predI : ℕ
  predJ : ℕ
  predLift : ℕ
  predDomain : HerzogLShapeDomain HD predI predJ
  value : normalizedGrid B e 0 predI predJ + routingC B e =
    normalizedGrid B e predLift i j

/-- Exact three-way inverse-`b` atlas, including both wrap regimes. -/
theorem canonicalPredecessorB_exists
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j) :
    Nonempty (CanonicalPredecessorB B e HD i j) := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  rcases hij with ⟨hiI, hjJ, hnotch⟩
  by_cases hi : 0 < i
  · refine ⟨{
      predI := i - 1
      predJ := j
      predLift := 0
      predDomain := ?_
      value := ?_ }⟩
    · unfold HerzogLShapeDomain
      omega
    · have hii : i - 1 + 1 = i := by omega
      have hib := congrArg (fun n => n * routingB B e) hii
      simp [normalizedGrid, Nat.add_mul] at hib ⊢
      omega
  · have hi0 : i = 0 := by omega
    by_cases hjt : cr23 HD ≤ j
    · refine ⟨{
        predI := L5A2C4A.c2 B e - 1
        predJ := j - cr23 HD
        predLift := cr21 HD
        predDomain := ?_
        value := ?_ }⟩
      · unfold HerzogLShapeDomain
        omega
      · have hr := (coherent_normalized_relations B e HD).2.1
        have hj : cr23 HD + (j - cr23 HD) = j := Nat.add_sub_of_le hjt
        have hjc := congrArg (fun n => n * routingC B e) hj
        have hI : L5A2C4A.c2 B e - 1 + 1 = L5A2C4A.c2 B e := by omega
        have hIb := congrArg (fun n => n * routingB B e) hI
        subst i
        simp [normalizedGrid, Nat.add_mul] at hr hjc hIb ⊢
        omega
    · refine ⟨{
        predI := cr12 HD - 1
        predJ := j + cr13 HD
        predLift := L5A2C4A.c1 B e
        predDomain := ?_
        value := ?_ }⟩
      · unfold HerzogLShapeDomain
        omega
      · have hr := (coherent_normalized_relations B e HD).1
        have hp' : cr12 HD - 1 + 1 = cr12 HD := by omega
        have hpb := congrArg (fun n => n * routingB B e) hp'
        subst i
        simp [normalizedGrid, Nat.add_mul] at hr hpb ⊢
        omega

/-- Exact three-way inverse-`c` atlas, including both wrap regimes. -/
theorem canonicalPredecessorC_exists
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j) :
    Nonempty (CanonicalPredecessorC B e HD i j) := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  rcases hij with ⟨hiI, hjJ, hnotch⟩
  by_cases hj : 0 < j
  · refine ⟨{
      predI := i
      predJ := j - 1
      predLift := 0
      predDomain := ?_
      value := ?_ }⟩
    · unfold HerzogLShapeDomain
      omega
    · have hjj : j - 1 + 1 = j := by omega
      have hjc := congrArg (fun n => n * routingC B e) hjj
      simp [normalizedGrid, Nat.add_mul] at hjc ⊢
      omega
  · have hj0 : j = 0 := by omega
    by_cases his : cr32 HD ≤ i
    · refine ⟨{
        predI := i - cr32 HD
        predJ := L5A2C4A.c3 B e - 1
        predLift := cr31 HD
        predDomain := ?_
        value := ?_ }⟩
      · unfold HerzogLShapeDomain
        omega
      · have hr := (coherent_normalized_relations B e HD).2.2
        have hi : cr32 HD + (i - cr32 HD) = i := Nat.add_sub_of_le his
        have hib := congrArg (fun n => n * routingB B e) hi
        have hJ : L5A2C4A.c3 B e - 1 + 1 = L5A2C4A.c3 B e := by omega
        have hJc := congrArg (fun n => n * routingC B e) hJ
        subst j
        simp [normalizedGrid, Nat.add_mul] at hr hib hJc ⊢
        omega
    · refine ⟨{
        predI := i + cr12 HD
        predJ := cr13 HD - 1
        predLift := L5A2C4A.c1 B e
        predDomain := ?_
        value := ?_ }⟩
      · unfold HerzogLShapeDomain
        omega
      · have hr := (coherent_normalized_relations B e HD).1
        have hq : cr13 HD - 1 + 1 = cr13 HD := by omega
        have hqc := congrArg (fun n => n * routingC B e) hq
        subst j
        simp [normalizedGrid, Nat.add_mul] at hr hqc ⊢
        omega

namespace CanonicalPredecessorB

theorem residue (P : CanonicalPredecessorB B e HD i j) :
    gridResidue B e P.predI P.predJ + routingB B e = gridResidue B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) P.value
  simpa only [Nat.cast_add, normalizedGrid_mod] using h

end CanonicalPredecessorB

namespace CanonicalPredecessorC

theorem residue (P : CanonicalPredecessorC B e HD i j) :
    gridResidue B e P.predI P.predJ + routingC B e = gridResidue B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have h := congrArg (fun n : ℕ => (n : ZMod (routingA B e))) P.value
  simpa only [Nat.cast_add, normalizedGrid_mod] using h

end CanonicalPredecessorC

/-- Canonical Herzog coordinates are unique at a residue. -/
theorem canonicalCoordinates_unique
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j i' j' : ℕ}
    (hij : HerzogLShapeDomain HD i j)
    (hij' : HerzogLShapeDomain HD i' j')
    (hres : gridResidue B e i' j' = gridResidue B e i j) :
    i' = i ∧ j' = j := by
  have hmod : Int.ModEq (routingA B e)
      ((i' : ℤ) * routingB B e + (j' : ℤ) * routingC B e)
      ((i : ℤ) * routingB B e + (j : ℤ) * routingC B e) := by
    change (i' : ZMod (routingA B e)) * routingB B e +
        (j' : ZMod (routingA B e)) * routingC B e =
      (i : ZMod (routingA B e)) * routingB B e +
        (j : ZMod (routingA B e)) * routingC B e at hres
    have hnat : i' * routingB B e + j' * routingC B e ≡
        i * routingB B e + j * routingC B e [MOD routingA B e] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using hres)
    simpa only [Nat.cast_add, Nat.cast_mul] using
      (Int.natCast_modEq_iff.mpr hnat)
  have hcoords := GenericLShape.modEq_unique
    (routingA B e) (routingB B e) (routingC B e)
    (L5A2C4A.c2 B e) (L5A2C4A.c3 B e)
    (cr12 HD) (cr13 HD) (cr32 HD) (cr23 HD)
    (coherent_coefficients_positive B e HD).1
    (coherent_coefficients_positive B e HD).2.1
    (coherent_coefficients_positive B e HD).2.2.2.2.2
    (coherent_coefficients_positive B e HD).2.2.2.1
    (coherent_coefficients B e HD).2.1
    (coherent_coefficients B e HD).2.2
    (L5A2C4OR6.coherent_second_minimality B e HD)
    (L5A2C4OR6.coherent_third_minimality B e HD)
    (L5A2C4OR5.coherent_uniqueZeroInLShape B e HD)
    (L5A2C4OR6.inLShape_of_herzogDomain B e HD hij')
    (L5A2C4OR6.inLShape_of_herzogDomain B e HD hij) hmod
  exact ⟨by exact_mod_cast hcoords.1, by exact_mod_cast hcoords.2⟩

/-- The canonical inverse-`b` predecessor, including its total lift, is
unique. -/
theorem canonicalPredecessorB_unique
    (P Q : CanonicalPredecessorB B e HD i j) :
    P.predI = Q.predI ∧ P.predJ = Q.predJ ∧ P.predLift = Q.predLift := by
  have hres : gridResidue B e P.predI P.predJ =
      gridResidue B e Q.predI Q.predJ := by
    apply add_right_cancel (b := (routingB B e : ZMod (routingA B e)))
    exact P.residue.trans Q.residue.symm
  obtain ⟨hi, hj⟩ := canonicalCoordinates_unique B e HD
    P.predDomain Q.predDomain hres.symm
  have hvP := P.value
  have hvQ := Q.value
  rw [hi, hj] at hvQ
  have ha := routingA_pos B e
  simp [normalizedGrid] at hvP hvQ
  exact ⟨hi.symm, hj.symm, by nlinarith⟩

/-- The canonical inverse-`c` predecessor, including its total lift, is
unique. -/
theorem canonicalPredecessorC_unique
    (P Q : CanonicalPredecessorC B e HD i j) :
    P.predI = Q.predI ∧ P.predJ = Q.predJ ∧ P.predLift = Q.predLift := by
  have hres : gridResidue B e P.predI P.predJ =
      gridResidue B e Q.predI Q.predJ := by
    apply add_right_cancel (b := (routingC B e : ZMod (routingA B e)))
    exact P.residue.trans Q.residue.symm
  obtain ⟨hi, hj⟩ := canonicalCoordinates_unique B e HD
    P.predDomain Q.predDomain hres.symm
  have hvP := P.value
  have hvQ := Q.value
  rw [hi, hj] at hvQ
  have ha := routingA_pos B e
  simp [normalizedGrid] at hvP hvQ
  exact ⟨hi.symm, hj.symm, by nlinarith⟩

/-- The two incoming arms of a forward packet are its canonical north/east
cells, with their exact total lifts.  This is the target incoming packet and
does not classify the target by outer-interiority. -/
theorem forwardPacket_target_incoming
    (P : CanonicalForwardPacket B e HD i j) :
    (normalizedGrid B e P.nLift P.nI P.nJ + routingB B e =
        normalizedGrid B e P.qLift P.qI P.qJ) ∧
      (normalizedGrid B e P.eLift P.eI P.eJ + routingC B e =
        normalizedGrid B e P.qLift P.qI P.qJ) := by
  constructor
  · have hn := P.nValue
    have hq := P.qValue
    simp [normalizedGrid] at hn hq ⊢
    omega
  · have he := P.eValue
    have hq := P.qValue
    simp [normalizedGrid] at he hq ⊢
    omega

/-- The incoming `b` tail carry is exactly the difference of total packet
lifts.  The subtraction-free equality is valid at every wrap. -/
theorem forwardPacket_tailBCarry
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    P.nLift + tailBCarry B e (gridResidue B e P.nI P.nJ) = P.qLift := by
  have hn := P.nAlpha hbase
  have hq := P.qAlpha hbase
  have ht := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e)
    (gridResidue B e P.nI P.nJ)
  change physicalAlpha B e (gridResidue B e P.nI P.nJ) + routingB B e =
    physicalAlpha B e (gridResidue B e P.nI P.nJ + routingB B e) +
      (routingA B e : ℤ) * tailBCarry B e (gridResidue B e P.nI P.nJ) at ht
  have hqres : gridResidue B e P.nI P.nJ + routingB B e =
      gridResidue B e P.qI P.qJ := by
    rw [P.nResidue, P.qResidue]
    abel
  rw [hqres] at ht
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod : (routingA B e : ℤ) *
      ((P.nLift : ℤ) + tailBCarry B e (gridResidue B e P.nI P.nJ) - P.qLift) = 0 := by
    linarith only [hn, ht, hq]
  have hz : (P.nLift : ℤ) + tailBCarry B e (gridResidue B e P.nI P.nJ) = P.qLift := by
    apply (sub_eq_zero.mp ?_)
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
  exact_mod_cast hz

/-- The incoming `c` tail carry is exactly the difference of total packet
lifts, again in subtraction-free form. -/
theorem forwardPacket_tailCCarry
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    P.eLift + tailCCarry B e (gridResidue B e P.eI P.eJ) = P.qLift := by
  have he := P.eAlpha hbase
  have hq := P.qAlpha hbase
  have ht := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e)
    (gridResidue B e P.eI P.eJ)
  change physicalAlpha B e (gridResidue B e P.eI P.eJ) + routingC B e =
    physicalAlpha B e (gridResidue B e P.eI P.eJ + routingC B e) +
      (routingA B e : ℤ) * tailCCarry B e (gridResidue B e P.eI P.eJ) at ht
  have hqres : gridResidue B e P.eI P.eJ + routingC B e =
      gridResidue B e P.qI P.qJ := by
    rw [P.eResidue, P.qResidue]
  rw [hqres] at ht
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod : (routingA B e : ℤ) *
      ((P.eLift : ℤ) + tailCCarry B e (gridResidue B e P.eI P.eJ) - P.qLift) = 0 := by
    linarith only [he, ht, hq]
  have hz : (P.eLift : ℤ) + tailCCarry B e (gridResidue B e P.eI P.eJ) = P.qLift := by
    apply (sub_eq_zero.mp ?_)
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
  exact_mod_cast hz

/-- R13 raw/tail dictionaries instantiated on both incoming arms. -/
theorem forwardPacket_raw_tail_dictionaries
    (P : CanonicalForwardPacket B e HD i j) :
    (L5A2C4C.eta B e P.nI P.nJ +
        tailBCarry B e (gridResidue B e P.nI P.nJ) =
      L5A2C4C.eta B e P.qI P.qJ +
        (routingData B e).u (gridResidue B e P.nI P.nJ)) ∧
    (L5A2C4C.eta B e P.eI P.eJ +
        tailCCarry B e (gridResidue B e P.eI P.eJ) =
      L5A2C4C.eta B e P.qI P.qJ +
        (routingData B e).v (gridResidue B e P.eI P.eJ)) := by
  constructor
  · exact raw_tail_b_dictionary_of_canonical_coordinates B e HD
      P.nDomain P.qDomain (by rw [P.nResidue, P.qResidue]; abel)
  · exact raw_tail_c_dictionary_of_canonical_coordinates B e HD
      P.eDomain P.qDomain (by rw [P.eResidue, P.qResidue])

/-- Accepted general incoming-cross formulas in integer, subtraction-safe
form.  No truncated natural subtraction is introduced. -/
theorem forwardPacket_cross_formulas
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    ((routingData B e).u (gridResidue B e P.nI P.nJ) : ℤ) =
        (P.qLift : ℤ) - (P.nLift : ℤ) +
          (L5A2C4C.eta B e P.nI P.nJ : ℤ) -
          (L5A2C4C.eta B e P.qI P.qJ : ℤ) ∧
      ((routingData B e).v (gridResidue B e P.eI P.eJ) : ℤ) =
        (P.qLift : ℤ) - (P.eLift : ℤ) +
          (L5A2C4C.eta B e P.eI P.eJ : ℤ) -
          (L5A2C4C.eta B e P.qI P.qJ : ℤ) := by
  have hd := forwardPacket_raw_tail_dictionaries P
  have hb := forwardPacket_tailBCarry P hbase
  have hc := forwardPacket_tailCCarry P hbase
  have hdB : (L5A2C4C.eta B e P.nI P.nJ : ℤ) +
      tailBCarry B e (gridResidue B e P.nI P.nJ) =
      L5A2C4C.eta B e P.qI P.qJ +
        (routingData B e).u (gridResidue B e P.nI P.nJ) := by exact_mod_cast hd.1
  have hdC : (L5A2C4C.eta B e P.eI P.eJ : ℤ) +
      tailCCarry B e (gridResidue B e P.eI P.eJ) =
      L5A2C4C.eta B e P.qI P.qJ +
        (routingData B e).v (gridResidue B e P.eI P.eJ) := by exact_mod_cast hd.2
  have hbI : (P.nLift : ℤ) +
      tailBCarry B e (gridResidue B e P.nI P.nJ) = P.qLift := by exact_mod_cast hb
  have hcI : (P.eLift : ℤ) +
      tailCCarry B e (gridResidue B e P.eI P.eJ) = P.qLift := by exact_mod_cast hc
  constructor <;> omega

/-- The base-to-east ambient tail carry is the packet's east lift. -/
theorem forwardPacket_base_tailBCarry
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    tailBCarry B e (gridResidue B e i j) = P.eLift := by
  have he := P.eAlpha hbase
  have ht := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) (gridResidue B e i j)
  change physicalAlpha B e (gridResidue B e i j) + routingB B e =
    physicalAlpha B e (gridResidue B e i j + routingB B e) +
      (routingA B e : ℤ) * tailBCarry B e (gridResidue B e i j) at ht
  rw [← P.eResidue] at ht
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hz : (routingA B e : ℤ) *
      ((tailBCarry B e (gridResidue B e i j) : ℤ) - P.eLift) = 0 := by
    linarith only [he, ht]
  have : (tailBCarry B e (gridResidue B e i j) : ℤ) = P.eLift := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
  exact_mod_cast this

/-- The base-to-north ambient tail carry is the packet's north lift. -/
theorem forwardPacket_base_tailCCarry
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j) :
    tailCCarry B e (gridResidue B e i j) = P.nLift := by
  have hn := P.nAlpha hbase
  have ht := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) (gridResidue B e i j)
  change physicalAlpha B e (gridResidue B e i j) + routingC B e =
    physicalAlpha B e (gridResidue B e i j + routingC B e) +
      (routingA B e : ℤ) * tailCCarry B e (gridResidue B e i j) at ht
  rw [← P.nResidue] at ht
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hz : (routingA B e : ℤ) *
      ((tailCCarry B e (gridResidue B e i j) : ℤ) - P.nLift) = 0 := by
    linarith only [hn, ht]
  have : (tailCCarry B e (gridResidue B e i j) : ℤ) = P.nLift := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
  exact_mod_cast this

/-- A branch seed with zero outgoing raw carries realizes its east/north
successor heights by adding the exact packet lifts. -/
theorem forwardPacket_zero_branch_successor_heights
    (P : CanonicalForwardPacket B e HD i j)
    (hbase : HerzogLShapeDomain HD i j)
    (hu : (routingData B e).u (gridResidue B e i j) = 0)
    (hv : (routingData B e).v (gridResidue B e i j) = 0) :
    L5A2C4C.eta B e i j + P.eLift = L5A2C4C.eta B e P.eI P.eJ ∧
      L5A2C4C.eta B e i j + P.nLift = L5A2C4C.eta B e P.nI P.nJ := by
  have hb := raw_tail_b_dictionary_of_canonical_coordinates B e HD
    hbase P.eDomain P.eResidue
  have hc := raw_tail_c_dictionary_of_canonical_coordinates B e HD
    hbase P.nDomain P.nResidue
  rw [forwardPacket_base_tailBCarry P hbase, hu, add_zero] at hb
  rw [forwardPacket_base_tailCCarry P hbase, hv, add_zero] at hc
  exact ⟨hb, hc⟩

/-- A positive surviving-notch branch seed can occur only in the ordinary,
upper-right, or bottom-top rows.  The five exclusions use the actual zero
corners and the actual `H0 < c1` wall; no location conclusion is assumed. -/
theorem positive_zero_branch_location
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j) (k : CanonicalLocation)
    (hk : CanonicalLocation.Holds HD k i j)
    (heta : 0 < L5A2C4C.eta B e i j)
    (hu : (routingData B e).u (gridResidue B e i j) = 0)
    (hv : (routingData B e).v (gridResidue B e i j) = 0)
    (hP : coherentP1 B e HD = 0) (hQ : coherentQ1 B e HD = 0)
    (hH : L5A2C4C.H0 B e < L5A2C4A.c1 B e) :
    k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop := by
  cases k with
  | ordinary => exact Or.inl rfl
  | upperRight => exact Or.inr (Or.inl rfl)
  | bottomTop => exact Or.inr (Or.inr rfl)
  | center =>
      let P := centerForwardPacket B e HD i j hk
      have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
      have hzero : L5A2C4C.eta B e P.eI P.eJ = 0 := by
        change L5A2C4C.eta B e (cr12 HD) (cr13 HD - 1) = 0
        exact hQ
      dsimp [P, centerForwardPacket] at hz hzero
      omega
  | upperArmInterior =>
      let P := upperArmForwardPacket B e HD i j hk
      have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
      change i + 1 = cr12 HD ∧ cr13 HD ≤ j ∧ j + 1 < L5A2C4A.c3 B e at hk
      have hmono := L5A2C4C.eta_antitone_right B e
        (cr12 HD - 1) (cr13 HD) (j + 1 - cr13 HD)
      have hcoord : cr13 HD + (j + 1 - cr13 HD) = j + 1 :=
        Nat.add_sub_of_le (by omega)
      have hzero : L5A2C4C.eta B e (cr12 HD - 1) (j + 1) = 0 := by
        rw [hcoord] at hmono
        have : L5A2C4C.eta B e (cr12 HD - 1) (j + 1) ≤
            coherentP1 B e HD := by simpa [coherentP1] using hmono
        omega
      dsimp [P, upperArmForwardPacket] at hz
      omega
  | bottomNotchInterior =>
      let P := bottomNotchForwardPacket B e HD i j hk
      have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
      change j + 1 = cr13 HD ∧ cr12 HD ≤ i ∧ i + 1 < L5A2C4A.c2 B e at hk
      have hmono := L5A2C4C.eta_antitone_left B e
        (cr12 HD) (cr13 HD - 1) (i + 1 - cr12 HD)
      have hcoord : cr12 HD + (i + 1 - cr12 HD) = i + 1 :=
        Nat.add_sub_of_le (by omega)
      have hzero : L5A2C4C.eta B e (i + 1) (cr13 HD - 1) = 0 := by
        rw [hcoord] at hmono
        have : L5A2C4C.eta B e (i + 1)
            (cr13 HD - 1) ≤ coherentQ1 B e HD := by
          simpa [coherentQ1] using hmono
        omega
      dsimp [P, bottomNotchForwardPacket] at hz
      omega
  | kappa1 =>
      let P := kappa1ForwardPacket B e HD i j hk
      have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
      have hcap := eta_le_H0 B e P.nI P.nJ
      dsimp [P, kappa1ForwardPacket] at hz hcap
      omega
  | kappa2 =>
      let P := kappa2ForwardPacket B e HD i j hk
      have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
      have hcap := eta_le_H0 B e P.eI P.eJ
      dsimp [P, kappa2ForwardPacket] at hz hcap
      omega

/-- Exact ordinary-row positive-seed formula and cap. -/
theorem ordinary_positive_seed_cap
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j)
    (hk : CanonicalLocation.Holds HD .ordinary i j)
    (heta : 0 < L5A2C4C.eta B e i j)
    (hu : (routingData B e).u (gridResidue B e i j) = 0)
    (hv : (routingData B e).v (gridResidue B e i j) = 0)
    (hw : 0 < (routingData B e).u
      (gridResidue B e i (j + 1)))
    (hH : L5A2C4C.H0 B e < L5A2C4A.c1 B e) :
    let P := ordinaryForwardPacket B e HD i j hk
    ((routingData B e).u (gridResidue B e P.nI P.nJ) : ℤ) =
        (L5A2C4C.eta B e i j : ℤ) - L5A2C4C.eta B e P.qI P.qJ ∧
      (routingData B e).u (gridResidue B e P.nI P.nJ) ≤ L5A2C4C.H0 B e ∧
      L5A2C4C.H0 B e < L5A2C4A.c1 B e ∧
      0 < L5A2C4C.eta B e P.eI P.eJ ∧
      0 < L5A2C4C.eta B e P.nI P.nJ := by
  let P := ordinaryForwardPacket B e HD i j hk
  have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
  have hc := forwardPacket_cross_formulas P hij
  have hcap := eta_le_H0 B e i j
  have hnres : gridResidue B e P.nI P.nJ = gridResidue B e i (j + 1) := by
    rw [P.nResidue]
    simpa using (gridResidue_add_c B e i j).symm
  have hwP : 0 < (routingData B e).u (gridResidue B e P.nI P.nJ) := by
    rw [hnres]
    exact hw
  dsimp [P, ordinaryForwardPacket] at hz hc hwP ⊢
  constructor
  · omega
  constructor
  · omega
  exact ⟨hH, by omega, by omega⟩

/-- Exact upper-right-row positive-seed formula and cap. -/
theorem upperRight_positive_seed_cap
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j)
    (hk : CanonicalLocation.Holds HD .upperRight i j)
    (heta : 0 < L5A2C4C.eta B e i j)
    (hu : (routingData B e).u (gridResidue B e i j) = 0)
    (hv : (routingData B e).v (gridResidue B e i j) = 0)
    (hw : 0 < (routingData B e).u
      (gridResidue B e i (j + 1)))
    (hH : L5A2C4C.H0 B e < L5A2C4A.c1 B e) :
    let P := upperRightForwardPacket B e HD i j hk
    ((routingData B e).u (gridResidue B e P.nI P.nJ) : ℤ) =
        (L5A2C4C.eta B e P.eI P.eJ : ℤ) - L5A2C4C.eta B e P.qI P.qJ ∧
      (routingData B e).u (gridResidue B e P.nI P.nJ) ≤ L5A2C4C.H0 B e ∧
      L5A2C4C.H0 B e < L5A2C4A.c1 B e ∧
      0 < L5A2C4C.eta B e P.eI P.eJ ∧
      0 < L5A2C4C.eta B e P.nI P.nJ := by
  let P := upperRightForwardPacket B e HD i j hk
  have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
  have hc := forwardPacket_cross_formulas P hij
  have hcap := eta_le_H0 B e P.eI P.eJ
  have hnres : gridResidue B e P.nI P.nJ = gridResidue B e i (j + 1) := by
    rw [P.nResidue]
    simpa using (gridResidue_add_c B e i j).symm
  have hwP : 0 < (routingData B e).u (gridResidue B e P.nI P.nJ) := by
    rw [hnres]
    exact hw
  change i + 1 = L5A2C4A.c2 B e ∧ j + 1 < cr13 HD at hk
  dsimp [P, upperRightForwardPacket] at hz hc hcap hwP ⊢
  constructor
  · omega
  constructor
  · omega
  exact ⟨hH, by omega, by omega⟩

/-- Exact bottom-top-row positive-seed formula and cap. -/
theorem bottomTop_positive_seed_cap
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hij : HerzogLShapeDomain HD i j)
    (hk : CanonicalLocation.Holds HD .bottomTop i j)
    (heta : 0 < L5A2C4C.eta B e i j)
    (hu : (routingData B e).u (gridResidue B e i j) = 0)
    (hv : (routingData B e).v (gridResidue B e i j) = 0)
    (hw : 0 < (routingData B e).u
      (gridResidue B e i (j + 1)))
    (hH : L5A2C4C.H0 B e < L5A2C4A.c1 B e) :
    let P := bottomTopForwardPacket B e HD i j hk
    ((routingData B e).u (gridResidue B e P.nI P.nJ) : ℤ) =
        (L5A2C4C.eta B e P.nI P.nJ : ℤ) - L5A2C4C.eta B e P.qI P.qJ ∧
      (routingData B e).u (gridResidue B e P.nI P.nJ) ≤ L5A2C4C.H0 B e ∧
      L5A2C4C.H0 B e < L5A2C4A.c1 B e ∧
      0 < L5A2C4C.eta B e P.eI P.eJ ∧
      0 < L5A2C4C.eta B e P.nI P.nJ := by
  let P := bottomTopForwardPacket B e HD i j hk
  have hz := forwardPacket_zero_branch_successor_heights P hij hu hv
  have hc := forwardPacket_cross_formulas P hij
  have hcap := eta_le_H0 B e P.nI P.nJ
  have hnres : gridResidue B e P.nI P.nJ = gridResidue B e i (j + 1) := by
    rw [P.nResidue]
    simpa using (gridResidue_add_c B e i j).symm
  have hwP : 0 < (routingData B e).u (gridResidue B e P.nI P.nJ) := by
    rw [hnres]
    exact hw
  change j + 1 = L5A2C4A.c3 B e ∧ i + 1 < cr12 HD at hk
  dsimp [P, bottomTopForwardPacket] at hz hc hcap hwP ⊢
  constructor
  · omega
  constructor
  · omega
  exact ⟨hH, by omega, by omega⟩

/-- Actual R9/R10 source-hit adapter for the positive-seed cap.  The state is
kept as the branch seed; the diagonal target is never substituted for it. -/
theorem actual_sourceHit_positive_seed_cap
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit (routingData B e) incoming target.raw)
    (hpositive : 0 < physicalHeight B e
      (L5A2C4OR9.actualSourceHitState B e incoming target hit))
    (hP : coherentP1 B e HD = 0) (hQ : coherentQ1 B e HD = 0)
    (hH : L5A2C4C.H0 B e < L5A2C4A.c1 B e) :
    let D := routingData B e
    let r := L5A2C4OR9.actualSourceHitState B e incoming target hit
    ∃ i j k,
      HerzogLShapeDomain HD i j ∧ gridResidue B e i j = r ∧
      CanonicalLocation.Holds HD k i j ∧
      (k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop) ∧
      0 < D.u (D.c r) ∧ D.u (D.c r) ≤ L5A2C4C.H0 B e ∧
      L5A2C4C.H0 B e < L5A2C4A.c1 B e := by
  let D := routingData B e
  let r := L5A2C4OR9.actualSourceHitState B e incoming target hit
  have hd := actual_sourceHit_cm_shz_local_square_dictionary B e HD incoming target hit
  have hs := actual_sourceHit_is_branch_seed B e incoming target hit
  change ActualSourceHitSeedDictionary B e HD r at hd
  change D.IsBranch r ∧ D.u r = 0 ∧ D.v r = 0 ∧
    0 < D.u (D.c r) ∧ D.u (D.c r) = D.v (D.b r) ∧
    branchDiagonalTarget B e r = D.b (D.c r) at hs
  rcases hd with ⟨i, j, k, hij, hres, hk, _huniq, _hw, hwpos, _hopp⟩
  have heta : 0 < L5A2C4C.eta B e i j := by
    rw [L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hij]
    rw [hres]
    exact hpositive
  have hloc := positive_zero_branch_location B e HD hij k hk heta
    (by rw [hres]; exact hs.2.1) (by rw [hres]; exact hs.2.2.1) hP hQ hH
  have hcstate : D.c r = gridResidue B e i (j + 1) := by
    rw [← hres]
    simpa [D, routingData, AperyStepData.toResidueData,
      RelativeIdeal.toAperyStepData] using (gridResidue_add_c B e i j).symm
  have hwgrid : 0 < D.u (gridResidue B e i (j + 1)) := by
    rw [← hcstate]
    exact hwpos
  have hlocOut := hloc
  have hwcap : D.u (D.c r) ≤ L5A2C4C.H0 B e := by
    rcases hloc with rfl | rfl | rfl
    · have h := ordinary_positive_seed_cap B e HD hij hk heta
        (by rw [hres]; exact hs.2.1) (by rw [hres]; exact hs.2.2.1) hwgrid hH
      have hn := (ordinaryForwardPacket B e HD i j hk).nResidue
      dsimp only at h
      have hngrid : gridResidue B e (ordinaryForwardPacket B e HD i j hk).nI
          (ordinaryForwardPacket B e HD i j hk).nJ = gridResidue B e i (j + 1) := by
        rw [hn]
        simpa using (gridResidue_add_c B e i j).symm
      rw [hngrid, ← hcstate] at h
      simpa [D] using h.2.1
    · have h := upperRight_positive_seed_cap B e HD hij hk heta
        (by rw [hres]; exact hs.2.1) (by rw [hres]; exact hs.2.2.1) hwgrid hH
      have hn := (upperRightForwardPacket B e HD i j hk).nResidue
      dsimp only at h
      have hngrid : gridResidue B e (upperRightForwardPacket B e HD i j hk).nI
          (upperRightForwardPacket B e HD i j hk).nJ = gridResidue B e i (j + 1) := by
        rw [hn]
        simpa using (gridResidue_add_c B e i j).symm
      rw [hngrid, ← hcstate] at h
      simpa [D] using h.2.1
    · have h := bottomTop_positive_seed_cap B e HD hij hk heta
        (by rw [hres]; exact hs.2.1) (by rw [hres]; exact hs.2.2.1) hwgrid hH
      have hn := (bottomTopForwardPacket B e HD i j hk).nResidue
      dsimp only at h
      have hngrid : gridResidue B e (bottomTopForwardPacket B e HD i j hk).nI
          (bottomTopForwardPacket B e HD i j hk).nJ = gridResidue B e i (j + 1) := by
        rw [hn]
        simpa using (gridResidue_add_c B e i j).symm
      rw [hngrid, ← hcstate] at h
      simpa [D] using h.2.1
  exact ⟨i, j, k, hij, hres, hk, hlocOut, hwpos, hwcap, hH⟩

end NS25Lean.L5A2C4OR14
