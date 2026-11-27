import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Rep.Basic
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisCovers

/-! Scheme automorphisms of a finite Galois cover act on actual sheaf sections. -/

namespace ManuscriptAudit.GaloisCoverAction

open CategoryTheory AlgebraicGeometry Opposite
open FieldEtaleGaloisCovers

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [Module.Finite K L] [IsGalois K L]

def automorphism (σ : L ≃ₐ[K] L) : galoisObject K L ⟶ galoisObject K L :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => σ.commutes x)

theorem automorphism_one : automorphism K L 1 = 𝟙 _ := by
  apply ((Scheme.Etale.forget (Spec (CommRingCat.of K))) ⋙ Over.forget _).map_injective
  change Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 _
  exact Spec.map_id _

theorem automorphism_mul (σ τ : L ≃ₐ[K] L) :
    automorphism K L (σ * τ) = automorphism K L σ ≫ automorphism K L τ := by
  apply ((Scheme.Etale.forget (Spec (CommRingCat.of K))) ⋙ Over.forget _).map_injective
  change Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  rw [← Spec.map_comp]
  rfl

variable (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0})

private def representation :
    Representation ℤ (L ≃ₐ[K] L) (F.obj.obj (op (galoisObject K L))) where
  toFun σ := (F.obj.map (automorphism K L σ).op).hom.toIntLinearMap
  map_one' := by
    rw [automorphism_one]
    ext x
    simp
  map_mul' σ τ := by
    rw [automorphism_mul, op_comp, F.obj.map_comp]
    rfl

def sectionsRep : Rep ℤ (L ≃ₐ[K] L) := Rep.of (representation K L F)

theorem sectionsRep_rho_apply (σ : L ≃ₐ[K] L)
    (x : F.obj.obj (op (galoisObject K L))) :
    (sectionsRep K L F).ρ σ x = F.obj.map (automorphism K L σ).op x :=
  rfl

variable {F} {H : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0}}

def sectionsRepMap (m : F ⟶ H) : sectionsRep K L F ⟶ sectionsRep K L H :=
  Rep.ofHom
    { toLinearMap := (m.hom.app (op (galoisObject K L))).hom.toIntLinearMap
      isIntertwining' := fun σ => by
        ext x
        exact NatTrans.naturality_apply m.hom (automorphism K L σ).op x }

theorem sectionsRepMap_apply (m : F ⟶ H) (x : F.obj.obj (op (galoisObject K L))) :
    (sectionsRepMap K L m).hom x = m.hom.app _ x := rfl

end
end ManuscriptAudit.GaloisCoverAction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GaloisCoverAction.automorphism_one,
      ``ManuscriptAudit.GaloisCoverAction.automorphism_mul,
      ``ManuscriptAudit.GaloisCoverAction.sectionsRep_rho_apply,
      ``ManuscriptAudit.GaloisCoverAction.sectionsRepMap_apply] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
