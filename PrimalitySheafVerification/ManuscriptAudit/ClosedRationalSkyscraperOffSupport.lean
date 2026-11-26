import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionInsideStalk
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleGeometricBaseChange

/-!
# Geometric skyscraper stalks off a closed rational point

The geometric skyscraper restricts to zero on the open complement of
the closed point, because no pointed lift from its defining geometric
point can land in any étale object over that complement.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] [IsSepClosed K]
variable {X : Scheme.{u}} (o : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion o]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- A geometric stalk off the closed image of a rational point is zero
for the genuine skyscraper at that point. -/
theorem closedRationalSkyscraper_stalk_isZero
    (hs : Disjoint (Set.range s) (Set.range o))
    (M : AddCommGrpCat.{u}) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj ((Scheme.pointSmallEtale o).skyscraperSheaf M)) := by
  let U : X.Opens := ⟨(Set.range o)ᶜ, o.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := U.ι
  have hrange : Set.range j = (Set.range o)ᶜ := by
    change (j.opensRange : Set X) = (Set.range o)ᶜ
    rw [show j.opensRange = U from Scheme.Opens.opensRange_ι U]
    rfl
  have hRange : Set.range s ⊆ Set.range j := by
    rw [hrange]
    exact Set.disjoint_left.mp hs
  let t := IsOpenImmersion.lift j s hRange
  have ht : t ≫ j = s := IsOpenImmersion.lift_fac _ _ _
  let Φ := Scheme.pointSmallEtale t
  let Ψ := Scheme.pointSmallEtale o
  let F := Ψ.skyscraperSheaf M
  let Q := (restriction j AddCommGrpCat.{u}).obj F
  have hValue (B : U.toScheme.Etale) : IsZero (Q.obj.obj (op B)) := by
    change IsZero (∏ᶜ fun _ : Ψ.fiber.obj ((etalePostcompose j).obj B) => M)
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro b
    have h : b.left ≫ (B.hom ≫ j) = o := Over.w b
    let x : Spec (CommRingCat.of K) := default
    have eq : j (B.hom (b.left x)) = o x := by
      change (b.left ≫ (B.hom ≫ j)) x = o x
      exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ X => f x) h
    have hx : o x ∈ Set.range j := ⟨B.hom (b.left x), eq⟩
    rw [hrange] at hx
    exact (hx ⟨x, rfl⟩).elim
  have hRestrict : IsZero (Φ.sheafFiber.obj Q) := by
    rw [IsZero.iff_id_eq_zero]
    apply Φ.presheafFiber_hom_ext
    intro B b
    exact (hValue B).eq_of_src _ _
  rw [← ht]
  exact hRestrict.of_iso ((restrictionStalkNatIso j t).app F).symm

/-- Distinct underlying geometric points are disjoint from the closed rational point. -/
theorem closedRationalSkyscraper_stalk_isZero_of_ne
    (hs : s (default : Spec (.of Ω)) ≠ o (default : Spec (CommRingCat.of K)))
    (M : AddCommGrpCat.{u}) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj ((Scheme.pointSmallEtale o).skyscraperSheaf M)) := by
  apply closedRationalSkyscraper_stalk_isZero o s _ M
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hab⟩
  rw [Subsingleton.elim a default, Subsingleton.elim b default] at hab
  exact hs hab.symm

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmallEtaleGeometricBaseChange.closedRationalSkyscraper_stalk_isZero,
      ``ManuscriptAudit.SmallEtaleGeometricBaseChange.closedRationalSkyscraper_stalk_isZero_of_ne] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
