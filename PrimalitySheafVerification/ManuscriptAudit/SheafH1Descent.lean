import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Dimension shifting for native sheaf cohomology in degree one

A section of the cokernel of an injective embedding represents a degree-one
cohomology class. Its local lifts are described by a covering sieve. To prove
vanishing by descent, it suffices to show that every such global section lifts
globally.
-/

namespace ManuscriptAudit.SheafH1Descent

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite ConcreteCategory

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

/-- The connecting homomorphism evaluated on a global cokernel section. -/
noncomputable def connectingSection (x : (cokernel i).obj.obj (op T)) : Sheaf.H F 1 :=
  ((cokernelSequence_exact i).extClass.postcomp integerConstant (show 0 + 1 = 1 by rfl))
    ((Sheaf.H.equiv₀ (cokernel i) hT).symm x)

/-- An injective target makes the connecting homomorphism onto degree one. -/
theorem connectingSection_surjective [Injective I] :
    Function.Surjective (connectingSection i hT) := by
  intro x
  have hx : x.comp (Ext.mk₀ (cokernelSequence i).f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  have h := Ext.covariant_sequence_exact₁' (integerConstant (J := J))
    (cokernelSequence_exact i) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨y, hy⟩ := (h x).1 hx
  refine ⟨Sheaf.H.equiv₀ (cokernel i) hT y, ?_⟩
  unfold connectingSection
  rw [AddEquiv.symm_apply_apply]
  exact hy

/-- A cokernel section that lifts globally has zero connecting class. -/
theorem connectingSection_of_lift (z : I.obj.obj (op T)) :
    connectingSection i hT ((cokernel.π i).hom.app (op T) z) = 0 := by
  unfold connectingSection
  rw [← Sheaf.H.equiv₀_symm_naturality (hT := hT) (cokernel.π i) z]
  have h := Ext.covariant_sequence_exact₃' (integerConstant (J := J))
    (cokernelSequence_exact i) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact (h _).2 ⟨(Sheaf.H.equiv₀ I hT).symm z, rfl⟩

/-- Global lifts through the cokernel of an injective embedding imply vanishing. -/
theorem H1_subsingleton_of_global_lifts [Injective I] (hT : IsTerminal T)
    (h : Function.Surjective ((cokernel.π i).hom.app (op T))) :
    Subsingleton (Sheaf.H F 1) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := connectingSection_surjective i hT x
  obtain ⟨z, rfl⟩ := h y
  exact connectingSection_of_lift i hT z

end DimensionShift

section LocalLifts

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat.{w}]

/-- The morphisms on which a given cokernel section lifts form a covering sieve. -/
theorem cokernel_section_lift_sieve_mem {T : C} (x : (cokernel i).obj.obj (op T)) :
    Presheaf.imageSieve (cokernel.π i).hom x ∈ J T := by
  letI : Sheaf.IsLocallySurjective (cokernel.π i) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} (cokernel.π i)).mpr inferInstance
  exact Presheaf.imageSieve_mem J (cokernel.π i).hom (U := op T) x

/-- Once a local lift through a sheaf morphism is compatible on a
single covering arrow, it glues to a global lift of the prescribed section. -/
theorem exists_global_lift_of_compatible_cover {T U : C} (f : U ⟶ T)
    (hCover : Sieve.generate (Presieve.singleton f) ∈ J T)
    {Q : Sheaf J AddCommGrpCat.{w}} (q : I ⟶ Q)
    (x : Q.obj.obj (op T)) (y : I.obj.obj (op U))
    (hImage : q.hom.app (op U) y = Q.obj.map f.op x)
    (hCompat : ∀ {W : C} (g h : W ⟶ U), g ≫ f = h ≫ f →
      I.obj.map g.op y = I.obj.map h.op y) :
    ∃ z : I.obj.obj (op T), q.hom.app (op T) z = x := by
  let Fg := forget AddCommGrpCat.{w}
  have hI : Presieve.IsSheaf J (I.obj ⋙ Fg) :=
    (isSheaf_iff_isSheaf_of_type J (I.obj ⋙ Fg)).mp ((sheafCompose J Fg).obj I).property
  have hQ : Presieve.IsSheaf J (Q.obj ⋙ Fg) :=
    (isSheaf_iff_isSheaf_of_type J (Q.obj ⋙ Fg)).mp ((sheafCompose J Fg).obj Q).property
  obtain ⟨z, hz, _⟩ := (Presieve.isSheafFor_singleton.mp (hI.isSheafFor _ hCover)) y hCompat
  have hSep : Function.Injective ((Q.obj ⋙ Fg).map f.op) :=
    Presieve.isSeparatedFor_singleton.mp (hQ.isSheafFor _ hCover).isSeparatedFor
  refine ⟨z, hSep ?_⟩
  change I.obj.map f.op z = y at hz
  change Q.obj.map f.op (q.hom.app (op T) z) = Q.obj.map f.op x
  rw [← NatTrans.naturality_apply q.hom f.op z, hz]
  exact hImage

end LocalLifts

end ManuscriptAudit.SheafH1Descent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafH1Descent.connectingSection_surjective,
      ``ManuscriptAudit.SheafH1Descent.connectingSection_of_lift,
      ``ManuscriptAudit.SheafH1Descent.H1_subsingleton_of_global_lifts,
      ``ManuscriptAudit.SheafH1Descent.cokernel_section_lift_sieve_mem,
      ``ManuscriptAudit.SheafH1Descent.exists_global_lift_of_compatible_cover] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
