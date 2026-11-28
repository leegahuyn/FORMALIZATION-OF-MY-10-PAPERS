import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall
import PrimalitySheafVerification.ManuscriptAudit.AffineStageMatchingDescent
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeTensorMatchTransport

/-! A finite stage witness for matching on an actual chart's
self-intersection descends to a genuine relative étale stage. -/

namespace ManuscriptAudit.AffineEtaleStageMatchPresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleStageAlgebraColimit (algebraCocone algebraDiagram)
open AffineStageTensorCoproduct (tensorIso)
open AffineStageTensorLegs (algebraHom inl_tensorIso_hom inr_tensorIso_hom)
open AffineRelativeTensorMatchTransport (to_coproduct from_coproduct)
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {B D M N : Type u}
  [CommRing B] [CommRing D] [CommRing M] [CommRing N]
  [Algebra B D] [Algebra B M] [Algebra B N] [Algebra.Etale B M] [Algebra.Etale B N]
  [WeaklyEtale (structureMap B D)]

private abbrev R := CommRingCat.of B
private abbrev Q := CommRingCat.mkUnder (R (B := B)) N

/-- A witness entirely over the geometric base of the self-intersection. -/
abbrev RelativeWitness (v : M →ₐ[B] D) (p q : M →ₐ[B] N) : Prop :=
  ∃ (T : Stage B D) (m : M →ₐ[B] T.carrier)
    (r : N →ₐ[B] T.carrier ⊗[B] T.carrier),
    T.toChart.comp m = v ∧
      r.comp p = (includeLeft : T.carrier →ₐ[B] T.carrier ⊗[B] T.carrier).comp m ∧
      r.comp q = (includeRight : T.carrier →ₐ[B] T.carrier ⊗[B] T.carrier).comp m

set_option maxHeartbeats 3800000 in
/-- A matching diagram of finitely presented étale algebras descends from
the actual tensor square to one genuine relative étale stage. -/
theorem exists_match (hApprox : FiniteTupleApproximation B D)
    (v : M →ₐ[B] D) (f : N →ₐ[B] D ⊗[B] D) (p q : M →ₐ[B] N)
    (hp : f.comp p = (includeLeft : D →ₐ[B] D ⊗[B] D).comp v)
    (hq : f.comp q = (includeRight : D →ₐ[B] D ⊗[B] D).comp v) :
    RelativeWitness v p q := by
  letI : EssentiallySmall.{u} (Stage B D) := NativeAffineEtaleStageSmall.essentiallySmall_stage
  let i : Stage B D := Stage.of B D v
  let D₀ : Stage B D ⥤ Under (R (B := B)) := algebraDiagram
  let c : Cocone D₀ := algebraCocone
  let w : CommRingCat.mkUnder (R (B := B)) (D ⊗[B] D) ≅ c.pt ⨿ c.pt :=
    tensorIso (R := R (B := B)) D D
  let t : Q (B := B) (N := N) ⟶ c.pt ⨿ c.pt := AlgHom.toUnder (R := R (B := B)) f ≫ w.hom
  let l : D₀.obj i ⟶ Q (B := B) (N := N) := AlgHom.toUnder (R := R (B := B)) p
  let r : D₀.obj i ⟶ Q (B := B) (N := N) := AlgHom.toUnder (R := R (B := B)) q
  have hL : l ≫ t = c.ι.app i ≫ coprod.inl :=
    to_coproduct p f v (includeLeft : D →ₐ[B] D ⊗[B] D) coprod.inl
      (inl_tensorIso_hom (R := B) (S := D) (T := D)) hp
  have hR : r ≫ t = c.ι.app i ≫ coprod.inr :=
    to_coproduct q f v (includeRight : D →ₐ[B] D ⊗[B] D) coprod.inr
      (inr_tensorIso_hom (R := B) (S := D) (T := D)) hq
  have hPi : (D₀.obj i).hom.hom.FinitePresentation := by
    change (algebraMap B M).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hPq : (Q (B := B) (N := N)).hom.hom.FinitePresentation := by
    change (algebraMap B N).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hc : IsColimit c := AffineEtaleStageAlgebraColimit.isColimit_algebra hApprox
  obtain ⟨j, ij, g, _, hlj, hrj⟩ :=
    AffineStageMatchingDescent.exists_match_at_stage (D := D₀) (c := c) hc i hPi
      (Q (B := B) (N := N)) hPq l r t hL hR
  let z : CommRingCat.mkUnder (R (B := B)) (j.carrier ⊗[B] j.carrier) ≅
      D₀.obj j ⨿ D₀.obj j := tensorIso (R := R (B := B)) j.carrier j.carrier
  let e : N →ₐ[B] j.carrier ⊗[B] j.carrier := algebraHom (g ≫ z.inv)
  refine ⟨j, hom ij, e, ij.property, ?_, ?_⟩
  · exact from_coproduct p g (hom ij)
      (includeLeft : j.carrier →ₐ[B] j.carrier ⊗[B] j.carrier) coprod.inl
      (inl_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)) hlj
  · exact from_coproduct q g (hom ij)
      (includeRight : j.carrier →ₐ[B] j.carrier ⊗[B] j.carrier) coprod.inr
      (inr_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)) hrj

end
end ManuscriptAudit.AffineEtaleStageMatchPresentation

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.AffineEtaleStageMatchPresentation.exists_match
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
