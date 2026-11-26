import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionQuotient

/-!
# Exactness of the native nested-open cokernel sequence

The third object and projection of the actual quotient complex provide
its cokernel universal property. The first arrow is a monomorphism.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

private theorem exactAndEpiOfCokernelProjection {D : Type*} [Category* D] [Abelian D]
    (Q : ShortComplex D) (e : cokernel Q.f ≅ Q.X₃)
    (h : cokernel.π Q.f ≫ e.hom = Q.g) : Q.Exact ∧ Epi Q.g :=
  have hc : IsColimit (CokernelCofork.ofπ Q.g Q.zero) :=
    cokernel.cokernelIso Q.f Q.g e h
  ⟨Q.exact_of_g_is_cokernel hc, epi_of_isColimit_cofork hc⟩

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j] (M : AddCommGrpCat.{u})

attribute [local irreducible] nestedOpenConstantMap

set_option maxHeartbeats 500000 in
private theorem quotientMono : Mono (nestedOpenQuotientSequence i j M).f := by
  rw [nestedOpenQuotientSequence_f]
  exact nestedOpenConstantMap_mono j i M

set_option maxHeartbeats 500000 in
private def quotientCokernelIso :
    cokernel (nestedOpenQuotientSequence i j M).f ≅ (nestedOpenQuotientSequence i j M).X₃ :=
  Iso.refl _

set_option maxHeartbeats 500000 in
private theorem quotientProjection :
    cokernel.π (nestedOpenQuotientSequence i j M).f ≫ (quotientCokernelIso i j M).hom =
      (nestedOpenQuotientSequence i j M).g := by
  change cokernel.π (nestedOpenConstantMap i j M) ≫ 𝟙 _ =
    cokernel.π (nestedOpenConstantMap i j M)
  exact Category.comp_id _

set_option maxHeartbeats 500000 in
private theorem quotientExactAndEpi :
    (nestedOpenQuotientSequence i j M).Exact ∧ Epi (nestedOpenQuotientSequence i j M).g := by
  let Q : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    nestedOpenQuotientSequence.{u} i j M
  let e : cokernel Q.f ≅ Q.X₃ := quotientCokernelIso i j M
  have h : cokernel.π Q.f ≫ e.hom = Q.g := quotientProjection i j M
  exact exactAndEpiOfCokernelProjection
    (D := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) Q e h

set_option maxHeartbeats 500000 in
/-- The actual quotient sequence of nested extension-by-zero maps is short exact. -/
theorem nestedOpenQuotientSequence_shortExact : (nestedOpenQuotientSequence i j M).ShortExact :=
  ShortComplex.ShortExact.mk' (quotientExactAndEpi i j M).1 (quotientMono i j M)
    (quotientExactAndEpi i j M).2

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientSequence_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
