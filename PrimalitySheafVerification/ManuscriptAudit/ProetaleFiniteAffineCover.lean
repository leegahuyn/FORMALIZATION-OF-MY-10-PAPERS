import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCover

/-! A finite jointly surjective family of actual affine pro-étale
objects is a covering family of an affine object in the native site. -/

namespace ManuscriptAudit.ProetaleFiniteAffineCover

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {T : S.ProEt} [IsAffine T.left] {n : ℕ}
  (V : Fin n → S.ProEt) (a : ∀ i, V i ⟶ T)
  (hV : ∀ i, IsAffine (V i).left)
  (hCov : ∀ x : T.left, ∃ i, ∃ y : (V i).left, (a i).left y = x)

private theorem map_weaklyEtale (i : Fin n) : WeaklyEtale (a i).left := by
  letI : WeaklyEtale T.hom := T.prop
  letI : WeaklyEtale ((a i).left ≫ T.hom) := by
    rw [MorphismProperty.Over.w (a i)]
    exact (V i).prop
  exact WeaklyEtale.of_comp (a i).left T.hom

include hV hCov in
/-- The genuine native finite affine cover criterion. -/
theorem covering : Sieve.ofArrows V a ∈ Scheme.ProEt.topology S T := by
  let G := Scheme.ProEt.forget S ⋙ Over.forget S
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows V a).map G ∈ Scheme.proetalePrecoverage T.left
  rw [Presieve.map_ofArrows]
  let P : PreZeroHypercover T.left :=
    { I₀ := Fin n
      X := fun i ↦ (V i).left
      f := fun i ↦ (a i).left }
  have hp : P.presieve₀ ∈ Scheme.precoverage @WeaklyEtale T.left :=
    (Scheme.ofArrows_mem_precoverage_iff @WeaklyEtale).mpr ⟨hCov, map_weaklyEtale V a⟩
  let C : T.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨P, hp⟩
  letI (i : C.I₀) : QuasiCompact (C.f i) := by
    letI : IsAffine (V i).left := hV i
    exact inferInstanceAs (QuasiCompact (a i).left)
  letI : Finite C.I₀ := inferInstanceAs (Finite (Fin n))
  have hq : QuasiCompactCover C.toPreZeroHypercover := QuasiCompactCover.of_finite
  change P.presieve₀ ∈ Scheme.proetalePrecoverage T.left
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hq, hp⟩

end
end ManuscriptAudit.ProetaleFiniteAffineCover

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleFiniteAffineCover.covering
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
