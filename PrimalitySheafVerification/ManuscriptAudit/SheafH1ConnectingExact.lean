import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! Exactness for the native degree-one connecting section. -/

namespace ManuscriptAudit.SheafH1ConnectingExact

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite ConcreteCategory

open SheafH1Descent

universe u v w w'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I)

private noncomputable abbrev cokernelSequence : ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

private theorem cokernelSequence_exact [Mono i] : (cokernelSequence i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

section DimensionShift

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [Mono i]
variable {T : C} (hT : IsTerminal T)

private noncomputable abbrev integerConstant : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- The native connecting section map respects subtraction. -/
theorem connectingSection_sub (x y : (cokernel i).obj.obj (op T)) :
    connectingSection i hT (x - y) = connectingSection i hT x - connectingSection i hT y := by
  simp only [connectingSection, map_sub]

/-- A connecting class vanishes exactly when the global cokernel section lifts. -/
theorem connectingSection_eq_zero_iff (x : (cokernel i).obj.obj (op T)) :
    connectingSection i hT x = 0 ↔
      ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  constructor
  · intro hx
    unfold connectingSection at hx
    have h := Ext.covariant_sequence_exact₃' (integerConstant (J := J))
      (cokernelSequence_exact i) 0 1 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    obtain ⟨z, hz⟩ := (h _).1 hx
    refine ⟨(Sheaf.H.equiv₀ I hT) z, ((Sheaf.H.equiv₀ (cokernel i) hT).symm).injective ?_⟩
    rw [← Sheaf.H.equiv₀_symm_naturality (hT := hT), AddEquiv.symm_apply_apply]
    exact hz
  · rintro ⟨z, rfl⟩
    exact connectingSection_of_lift i hT z


end DimensionShift

end ManuscriptAudit.SheafH1ConnectingExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafH1ConnectingExact.connectingSection_sub,
      ``ManuscriptAudit.SheafH1ConnectingExact.connectingSection_eq_zero_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
