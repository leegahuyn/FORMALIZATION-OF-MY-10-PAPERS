import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechLowDifferentials
import PrimalitySheafVerification.ManuscriptAudit.SheafCechDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.SingletonCoverRefinement

/-! Exactness of the Čech complex over every singleton cover makes
actual local cokernel lifts descend to sections on the base. -/

namespace ManuscriptAudit.EtaleCechSectionLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleCechDirectSum InjectiveCechPullback SingletonCoverRefinement

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section Site

variable {C : Type*} [Category* C] [HasFiniteLimits C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{0}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{0})]
variable {D I : Sheaf J AddCommGrpCat.{0}} (i : D ⟶ I) [Mono i]

/-- A local lift of a cokernel section descends if the kernel Čech
complex is exact in degree one on that covering arrow. -/
theorem exists_global_lift_of_cech_exact {U T : C} (f : U ⟶ T)
    (hf : Covers J f) (h : (Cech f D.obj).ExactAt 1)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  obtain ⟨b, hb, hbCech⟩ := SheafCechCokernel.exists_cocycle_of_local_lift i f x y hy
  obtain ⟨a, ha⟩ := EtaleCechLowDifferentials.exists_boundary f D.obj h b hbCech
  let W := Double f
  let k := i.hom.app (op U)
  let y' := y - k a
  have hDiff : I.obj.map (second f).op (k a) - I.obj.map (first f).op (k a) =
      I.obj.map (second f).op y - I.obj.map (first f).op y := by
    change I.obj.map (second f).op (i.hom.app (op U) a) -
      I.obj.map (first f).op (i.hom.app (op U) a) = _
    rw [← NatTrans.naturality_apply i.hom (second f).op a,
      ← NatTrans.naturality_apply i.hom (first f).op a]
    change (i.hom.app (op W)).hom _ - (i.hom.app (op W)).hom _ = _
    rw [← map_sub]
    exact (congrArg (fun z ↦ i.hom.app (op W) z) ha.symm).trans hb
  have hCompat : I.obj.map (first f).op y' = I.obj.map (second f).op y' := by
    apply Eq.symm
    apply sub_eq_zero.mp
    change (I.obj.map (second f).op).hom (y - k a) -
      (I.obj.map (first f).op).hom (y - k a) = 0
    rw [map_sub, map_sub]
    calc
      _ = (I.obj.map (second f).op y - I.obj.map (first f).op y) -
        (I.obj.map (second f).op (k a) - I.obj.map (first f).op (k a)) := by abel
      _ = 0 := by rw [hDiff, sub_self]
  let π := cokernel.π i
  have hZero : π.hom.app (op U) (k a) = 0 :=
    ConcreteCategory.congr_hom (congrArg (fun e : D ⟶ cokernel i ↦ e.hom.app (op U))
      (cokernel.condition i)) a
  have hImage : π.hom.app (op U) y' = (cokernel i).obj.map f.op x := by
    change (π.hom.app (op U)).hom (y - k a) = _
    rw [map_sub]
    change π.hom.app (op U) y - π.hom.app (op U) (k a) = _
    rw [hZero, sub_zero]
    exact hy
  obtain ⟨z, hz⟩ := exists_amalgamation J I f hf y' hCompat
  refine ⟨z, restriction_injective J (cokernel i) f hf ?_⟩
  rw [← NatTrans.naturality_apply π.hom f.op z, hz]
  exact hImage

end Site

section Affine

variable {S : Scheme.{0}} [HasFiniteLimits S.AffineEtale]

private abbrev J := Scheme.AffineEtale.topology S
private abbrev C := Sheaf (J (S := S)) AddCommGrpCat.{0}

variable [(J (S := S)).HasSheafCompose (forget AddCommGrpCat.{0})]
variable [(J (S := S)).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Positive Čech acyclicity over actual singleton affine étale covers. -/
def AffineCechAcyclic (D : C (S := S)) : Prop :=
  ∀ {U T : S.AffineEtale} (f : U ⟶ T), Covers (J (S := S)) f →
    ∀ n : ℕ, (Cech f D.obj).ExactAt (n + 1)

/-- The quotient of an inclusion with a Čech-acyclic kernel is
surjective on sections of every affine étale object. -/
theorem affine_cokernel_sections_surjective {D I : C (S := S)}
    (h : AffineCechAcyclic D) (i : D ⟶ I) [Mono i] (T : S.AffineEtale) :
    Function.Surjective ((cokernel.π i).hom.app (op T)) := by
  letI : Sheaf.IsLocallySurjective (cokernel.π i) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{0} (cokernel.π i)).mpr inferInstance
  intro x
  obtain ⟨U, f, hf, y, hy⟩ :=
    AffineEtaleSingletonLift.exists_singleton_cover_lift (U := T) (cokernel.π i) x
  exact exists_global_lift_of_cech_exact i f hf (h f hf 0) x y hy

/-- In degree one, singleton Čech acyclicity implies ordinary
affine étale cohomological acyclicity. -/
theorem affine_HOne_subsingleton {D I : C (S := S)}
    [HasExt.{0} (C (S := S))] (h : AffineCechAcyclic D)
    (i : D ⟶ I) [Mono i] [Injective I] {T : S.AffineEtale} (hT : IsTerminal T) :
    Subsingleton (Sheaf.H D 1) :=
  SheafH1Descent.H1_subsingleton_of_global_lifts i hT
    (affine_cokernel_sections_surjective h i T)

end Affine

end

end ManuscriptAudit.EtaleCechSectionLifts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleCechSectionLifts.exists_global_lift_of_cech_exact,
      ``ManuscriptAudit.EtaleCechSectionLifts.affine_cokernel_sections_surjective,
      ``ManuscriptAudit.EtaleCechSectionLifts.affine_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
