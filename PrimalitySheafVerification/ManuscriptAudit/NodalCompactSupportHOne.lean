import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportProjectiveComparison

/-! The compact-support extension of the actual affine node along its
proper compactification has the same degree-one cohomology as the
proper node over a separably closed field. -/

namespace ManuscriptAudit.NodalCompactSupportHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalRationalInfinity (infinityPoint infinityPoint_isClosedImmersion affine_complement_eq_infinity)
open OpenEtaleExtension SmallEtaleGeometricBaseChange GeometricSkyscraperCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

universe u
private abbrev C := AddCommGrpCat.{u}

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev P := projectiveNode K
private abbrev o := infinityPoint K ≫ 𝟙 (P K)

private theorem infinity_closed : IsClosedImmersion (o K) := by
  simpa only [o, Category.comp_id] using infinityPoint_isClosedImmersion K

private theorem affine_range : Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ := by
  simpa using congrArg (fun W : Set (P K) => Wᶜ) (affine_complement_eq_infinity K)

private def infinitySequence (M : C.{u}) :
    ShortComplex (Sheaf (P K).smallEtaleTopology C.{u}) :=
  letI := infinity_closed K
  nestedOpenRationalOriginSequence (affineOpen K) (𝟙 (P K)) M (infinityPoint K) (affine_range K)

private theorem infinitySequence_shortExact (M : C.{u}) : (infinitySequence K M).ShortExact := by
  letI := infinity_closed K
  exact nestedOpenRationalOriginSequence_shortExact (affineOpen K) (𝟙 (P K)) M
    (infinityPoint K) (affine_range K)

private theorem infinitySequence_HZero_surjective (M : C.{u}) :
    Function.Surjective (Sheaf.H.map (infinitySequence K M).g 0) := by
  letI := infinity_closed K
  exact rationalPointQuotient_HZero_surjective (affineOpen K) M (infinityPoint K) (affine_range K)

private theorem infinitySequence_boundary_HOne (M : C.{u}) :
    Subsingleton (Sheaf.H (infinitySequence K M).X₃ 1) := by
  let Φ := Scheme.pointSmallEtale (o K)
  let e₀ : (infinitySequence K M).X₃ ≅ Φ.skyscraperSheaf M :=
    rationalPointConstantDirectImageIso K (o K) M
  let e := ((Sheaf.functorH (P K).smallEtaleTopology 1).mapIso e₀).addCommGroupIsoToAddEquiv
  have h := geometricSkyscraperH_succ_subsingleton Φ M 0
  exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩

private theorem infinitySequence_HOne_bijective (M : C.{u}) :
    Function.Bijective (Sheaf.H.map (infinitySequence K M).f 1) := by
  let S := infinitySequence K M
  let hS := infinitySequence_shortExact K M
  let Z := (constantSheaf (P K).smallEtaleTopology C.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hExact : Function.Exact (Sheaf.H.map S.g 0)
      (hS.extClass.postcomp Z (show 0 + 1 = 1 from rfl)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₃' Z hS 0 1 rfl)
  constructor
  · intro x y hxy
    have hz : (Sheaf.H.map S.f 1) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS (x - y) hz rfl
    exact sub_eq_zero.mp (ht.symm.trans ((hExact t).mpr (infinitySequence_HZero_surjective K M t)))
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero 1) = 0 :=
      (infinitySequence_boundary_HOne K M).allEq _ _
    exact Ext.covariant_sequence_exact₂ (X := Z) hS y hy

/-- Actual étale compact support via the checked proper nodal compactification. -/
abbrev nodalHc (M : C.{u}) (n : ℕ) :=
  Sheaf.H ((extensionByZero (affineOpen K) C.{u}).obj
    ((constantSheaf (affineNode K).smallEtaleTopology C.{u}).obj M)) n

/-- The degree-one comparison induced by extension by zero into the actual proper node. -/
def nodalHcOneProjectiveEquiv (M : C.{u}) :
    nodalHc K M 1 ≃+
      Sheaf.H ((constantSheaf (P K).smallEtaleTopology C.{u}).obj M) 1 := by
  let J := extensionByZero (affineOpen K) C.{u}
  let G := (constantSheaf (affineNode K).smallEtaleTopology C.{u}).obj M
  let T := (constantSheaf (P K).smallEtaleTopology C.{u}).obj M
  let S := infinitySequence K M
  let e₁ : S.X₁ ≅ J.obj G :=
    ((extensionByZeroCompIso (affineOpen K) (𝟙 (P K))).symm.app G) ≪≫
      (extensionByZeroIdIso (P K)).app (J.obj G)
  let e₂ : S.X₂ ≅ T := (extensionByZeroIdIso (P K)).app T
  let H := Sheaf.functorH (P K).smallEtaleTopology 1
  exact ((H.mapIso e₁).addCommGroupIsoToAddEquiv).symm.trans
    ((AddEquiv.ofBijective (Sheaf.H.map S.f 1) (infinitySequence_HOne_bijective K M)).trans
      (H.mapIso e₂).addCommGroupIsoToAddEquiv)

end
end ManuscriptAudit.NodalCompactSupportHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalCompactSupportHOne.nodalHcOneProjectiveEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
