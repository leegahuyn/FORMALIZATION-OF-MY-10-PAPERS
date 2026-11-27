import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne

/-! The rational point at infinity is acyclic in positive degrees.
Thus the actual compact-support comparison for the affine node
identifies all positive degrees with ordinary cohomology of the proper node. -/

namespace ManuscriptAudit.NodalCompactSupportHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalRationalInfinity (infinityPoint infinityPoint_isClosedImmersion affine_complement_eq_infinity)
open OpenEtaleExtension SmallEtaleGeometricBaseChange GeometricSkyscraperCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

universe u

private abbrev Ab := AddCommGrpCat.{u}

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev X := projectiveNode K
private abbrev o := infinityPoint K ≫ 𝟙 (X K)

private theorem closedInfinity : IsClosedImmersion (o K) := by
  simpa only [o, Category.comp_id] using infinityPoint_isClosedImmersion K

private theorem complementInfinity : Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ := by
  simpa using congrArg (fun W : Set (X K) ↦ Wᶜ) (affine_complement_eq_infinity K)

private def boundarySequence (M : Ab.{u}) :
    ShortComplex (Sheaf (X K).smallEtaleTopology Ab.{u}) :=
  letI := closedInfinity K
  nestedOpenRationalOriginSequence (affineOpen K) (𝟙 (X K)) M (infinityPoint K) (complementInfinity K)

private theorem boundarySequence_shortExact (M : Ab.{u}) : (boundarySequence K M).ShortExact := by
  letI := closedInfinity K
  exact nestedOpenRationalOriginSequence_shortExact (affineOpen K) (𝟙 (X K)) M
    (infinityPoint K) (complementInfinity K)

private theorem boundaryAcyclic (M : Ab.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (boundarySequence K M).X₃ (n + 1)) := by
  let Φ := Scheme.pointSmallEtale (o K)
  let e : (boundarySequence K M).X₃ ≅ Φ.skyscraperSheaf M :=
    rationalPointConstantDirectImageIso K (o K) M
  let eH := ((Sheaf.functorH (X K).smallEtaleTopology (n + 1)).mapIso e).addCommGroupIsoToAddEquiv
  let h := geometricSkyscraperH_succ_subsingleton Φ M n
  exact ⟨fun x y ↦ eH.injective (h.elim _ _)⟩

private theorem higherInclusion_bijective (M : Ab.{u}) (n : ℕ) :
    Function.Bijective (Sheaf.H.map (boundarySequence K M).f (n + 2)) := by
  let S := boundarySequence K M
  let hS := boundarySequence_shortExact K M
  let Z := (constantSheaf (X K).smallEtaleTopology Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  constructor
  · intro x y hxy
    have hZero : Sheaf.H.map S.f (n + 2) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hZero' : (x - y).comp (Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := hZero
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS (x - y) hZero'
      (show (n + 1) + 1 = n + 2 by rfl)
    have hz₀ : z = 0 := (boundaryAcyclic K M n).elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz₀, Ext.zero_comp]
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero (n + 2)) = 0 :=
      (boundaryAcyclic K M (n + 1)).elim _ _
    exact Ext.covariant_sequence_exact₂ (X := Z) hS y hy

/-- The actual compact-support cohomology of the affine nodal model and
the ordinary cohomology of its proper closure agree in degree at least two. -/
def nodalHcHigherProjectiveEquiv (M : Ab.{u}) (n : ℕ) :
    nodalHc K M (n + 2) ≃+
      Sheaf.H ((constantSheaf (X K).smallEtaleTopology Ab.{u}).obj M) (n + 2) := by
  let F := (constantSheaf (affineNode K).smallEtaleTopology Ab.{u}).obj M
  let G := (constantSheaf (X K).smallEtaleTopology Ab.{u}).obj M
  let J := extensionByZero (affineOpen K) Ab.{u}
  let H := Sheaf.functorH (X K).smallEtaleTopology (n + 2)
  let S := boundarySequence K M
  let e₁ : S.X₁ ≅ J.obj F :=
    ((extensionByZeroCompIso (affineOpen K) (𝟙 (X K))).symm.app F) ≪≫
      (extensionByZeroIdIso (X K)).app (J.obj F)
  let e₂ : S.X₂ ≅ G := (extensionByZeroIdIso (X K)).app G
  let e := AddEquiv.ofBijective (Sheaf.H.map S.f (n + 2)) (higherInclusion_bijective K M n)
  exact (H.mapIso e₁).addCommGroupIsoToAddEquiv.symm.trans
    (e.trans (H.mapIso e₂).addCommGroupIsoToAddEquiv)

/-- Comparison with the actual proper nodal model in every positive degree. -/
def nodalHcSuccProjectiveEquiv (M : Ab.{u}) (n : ℕ) :
    nodalHc K M (n + 1) ≃+
      Sheaf.H ((constantSheaf (X K).smallEtaleTopology Ab.{u}).obj M) (n + 1) := by
  cases n with
  | zero => exact nodalHcOneProjectiveEquiv K M
  | succ n => exact nodalHcHigherProjectiveEquiv K M n

end

end ManuscriptAudit.NodalCompactSupportHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportHOne.nodalHcHigherProjectiveEquiv,
      ``ManuscriptAudit.NodalCompactSupportHOne.nodalHcSuccProjectiveEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
