import NS25Lean.P2BranchBFinalRepairKoszulSurgery

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.PrincipalTensorColonExact
open L5A2BFinalRepair
variable {k C V W : Type*} [Field k] [CommRing C] [Algebra k C]
  [CommRing V] [Algebra k V] [CommRing W] [Algebra k W]

/-- Structural exactness and generator compatibility of a principal module
sequence. No cohomology dimensions or desired estimate are included. -/
structure ExactData (C V W : Type*) [CommRing C] [Algebra k C]
    [CommRing V] [Algebra k V] [CommRing W] [Algebra k W] where
  c : Fin 3 → C
  a : Fin 3 → V
  b : Fin 3 → W
  i : C →ₗ[k] V
  p : V →ₗ[k] W
  injective : Function.Injective i
  surjective : Function.Surjective p
  exact : LinearMap.range i=LinearMap.ker p
  compat_i : ∀ j z, i (c j*z)=a j*i z
  compat_p : ∀ j z, p (a j*z)=b j*p z

abbrev PrefixH0 (S : ExactData (k:=k) C V W) := LinearMap.ker (threeKoszulD0 (k:=k) S.a)
abbrev FinalH0 (S : ExactData (k:=k) C V W) := LinearMap.ker (threeKoszulD0 (k:=k) S.b)
abbrev ColonH1 (S : ExactData (k:=k) C V W) := ThreeKoszulH1 (k:=k) S.c

def ColonH0 (S : ExactData (k:=k) C V W) : Submodule k C where
  carrier := {z | ∀ i, S.c i*z=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp [mul_add,hx i,hy i]
  smul_mem' := by intro r z hz i; simp [mul_smul_comm,hz i]

def linearLift (S : ExactData (k:=k) C V W) :
    W →ₗ[k] V :=
  ((S.p).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (S.surjective))).choose

theorem linearLift_spec (S : ExactData (k:=k) C V W) (z : W) :
    S.p (linearLift S z) = z :=
  LinearMap.congr_fun
    ((S.p).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (S.surjective))).choose_spec z

theorem retract_on_kernel (S : ExactData (k:=k) C V W)
    (z : V)
    (hz : S.p z = 0) :
    S.i
      ((S.i).leftInverse z) = z := by
  have hr : z ∈ LinearMap.range (S.i) := by
    rw [S.exact]
    exact hz
  obtain ⟨w,rfl⟩ := hr
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (S.injective))]

def connectingPre (S : ExactData (k:=k) C V W) :
    FinalH0 S →ₗ[k] (Fin 3 → C) where
  toFun := fun z i => (S.i).leftInverse
    (S.a i * linearLift S z.val)
  map_add' := by intro z w; ext i; simp [map_add,mul_add]
  map_smul' := by intro a z; ext i; simp [map_smul,mul_smul_comm]

theorem connectingPre_image (S : ExactData (k:=k) C V W) (z : FinalH0 S) (i : Fin 3) :
    S.i (connectingPre S z i) =
      S.a i * linearLift S z.val := by
  apply retract_on_kernel
  rw [S.compat_p,linearLift_spec]
  exact congrFun z.property i

theorem connectingPre_cycle (S : ExactData (k:=k) C V W) (z : FinalH0 S) :
    threeKoszulD1 (k:=k) (S.c)
      (connectingPre S z) = 0 := by
  have hc : ∀ i j : Fin 3,
      S.c j * connectingPre S z i -
      S.c i * connectingPre S z j = 0 := by
    intro i j
    apply S.injective
    rw [map_sub,map_zero,S.compat_i,S.compat_i,
      connectingPre_image,connectingPre_image]
    ring
  ext i
  fin_cases i <;> simpa [threeKoszulD1] using hc _ _

def connecting (S : ExactData (k:=k) C V W) :
    FinalH0 S →ₗ[k] ColonH1 S :=
  Submodule.mkQ _ ∘ₗ (connectingPre S).codRestrict _
    (connectingPre_cycle S)

def h0Projection (S : ExactData (k:=k) C V W) :
    PrefixH0 S →ₗ[k] FinalH0 S :=
  ((S.p).comp
    (PrefixH0 S).subtype).codRestrict _ (by
      intro z
      ext i
      change S.b i * S.p z.val = 0
      rw [← S.compat_p]
      have hz := congrFun z.property i
      change S.a i*z.val=0 at hz
      rw [hz,map_zero])

theorem connecting_eq_zero (S : ExactData (k:=k) C V W) (z : FinalH0 S) :
    connecting S z = 0 ↔
      ∃ w : C,
        threeKoszulD0 (k:=k) (S.c) w =
          connectingPre S z := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem connecting_exact (S : ExactData (k:=k) C V W) :
    LinearMap.range (h0Projection S) =
      LinearMap.ker (connecting S) := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩
    rw [LinearMap.mem_ker,connecting_eq_zero]
    let l := linearLift S
      (h0Projection S b).val
    let w := (S.i).leftInverse (l-b.val)
    have hw : S.i w = l-b.val := by
      apply retract_on_kernel
      rw [map_sub,linearLift_spec]
      exact sub_self _
    refine ⟨w,?_⟩
    ext i
    apply S.injective
    change S.i (S.c i*w) = _
    rw [S.compat_i,hw,connectingPre_image,mul_sub]
    have hb := congrFun b.property i
    change S.a i*b.val=0 at hb
    rw [hb,sub_zero]
  · intro hz
    obtain ⟨w,hw⟩ := (connecting_eq_zero S z).mp hz
    let b := linearLift S z.val - S.i w
    have hb : b ∈ PrefixH0 S := by
      ext i
      change S.a i*b=0
      dsimp [b]
      rw [mul_sub,← S.compat_i]
      have hwi := congrFun hw i
      change S.c i*w = _ at hwi
      rw [hwi,connectingPre_image,sub_self]
    refine ⟨⟨b,hb⟩,?_⟩
    apply Subtype.ext
    change S.p b = z.val
    dsimp [b]
    rw [map_sub,linearLift_spec]
    have hi : S.p (S.i w)=0 := by
      have hr : S.i w ∈ LinearMap.range (S.i) := ⟨w,rfl⟩
      rw [S.exact] at hr
      exact hr
    rw [hi,sub_zero]

def h0Injection (S : ExactData (k:=k) C V W) :
    ColonH0 S →ₗ[k] PrefixH0 S :=
  ((S.i).comp
    (ColonH0 S).subtype).codRestrict _ (by
      intro z
      ext i
      change S.a i * S.i z.val=0
      rw [← S.compat_i]
      have hz := z.property i
      change S.c i*z.val=0 at hz
      rw [hz,map_zero])

theorem h0Injection_injective (S : ExactData (k:=k) C V W) :
    Function.Injective (h0Injection S) := by
  intro z w he
  apply Subtype.ext
  exact S.injective (congrArg Subtype.val he)

theorem h0Projection_exact (S : ExactData (k:=k) C V W) :
    LinearMap.range (h0Injection S) =
      LinearMap.ker (h0Projection S) := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    have hr : S.i w.val ∈
        LinearMap.range (S.i) := ⟨w.val,rfl⟩
    rw [S.exact] at hr
    exact hr
  · intro hz
    have hz' : z.val ∈ LinearMap.range (S.i) := by
      rw [S.exact]
      exact congrArg Subtype.val hz
    obtain ⟨w,hw⟩ := hz'
    have hs : w ∈ ColonH0 S := by
      intro i
      change S.c i*w=0
      apply S.injective
      rw [S.compat_i,hw,map_zero]
      exact congrFun z.property i
    exact ⟨⟨w,hs⟩,Subtype.ext hw⟩


end NS25Lean.PrincipalTensorColonExact
