import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! Native continuous-coefficient pullback agrees with ordinary constant
coefficient pullback when the coefficients are discrete. -/

namespace ManuscriptAudit.ProetaleDiscreteSchemePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleDiscreteConstant (constantIso constantToContinuous constantIso_unit)
open ProetaleSchemeCohomologyPullback (constant continuous pullback pullback_naturality)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev J (Z : Scheme.{0}) := Scheme.ProEt.topology Z

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M]

private abbrev B := AddCommGrpCat.of (ULift.{1} M)
private abbrev C (Z : Scheme.{0}) := (constantSheaf (J Z) A).obj (B M)

private theorem evaluate_constant {Z : Scheme.{0}} {V : Z.ProEt} (hV : IsTerminal V) :
    (constantSheafAdj (J Z) A hV).homEquiv (B M) (functions M Z) (constantIso Z M).hom =
      (constantToContinuous Z M).app (op V) := by
  let b := sheafificationAdjunction (J Z) A
  let E := (Functor.const Z.ProEtᵒᵖ).obj (B M)
  have h : (b.homEquiv E (functions M Z)) (constantIso Z M).hom =
      constantToContinuous Z M := by
    rw [Adjunction.homEquiv_unit]
    exact constantIso_unit Z M
  let c := constantPresheafAdj A hV
  change (c.homEquiv (B M) (functions M Z).obj)
    ((b.homEquiv E (functions M Z)) (constantIso Z M).hom) = _
  rw [h, Adjunction.homEquiv_unit]
  change (𝟙 _) ≫ (constantToContinuous Z M).app (op V) = _
  rw [Category.id_comp]

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private theorem diagonal_label (V : Y.ProEt) :
    (constantToContinuous Y M).app (op V) ≫ (diagonal M f).hom.app (op V) =
      (constantToContinuous X M).app (op ((baseChange f).obj V)) := by
  apply AddCommGrpCat.ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

private abbrev a := ((adjunction f).homEquiv (functions M Y) (functions M X)).symm
  (diagonal M f)

set_option maxHeartbeats 6900000 in
/-- The actual discrete-coefficient identification commutes with the inverse images. -/
theorem coefficient_pullback :
    (inverseImage f).map (constantIso Y M).hom ≫ a M f =
      ((constantInverseImageIso f).app (B M)).hom ≫ (constantIso X M).hom := by
  let L := inverseImage f
  let R := directImage f A
  let ad := adjunction f
  let T := Scheme.ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale Y
  let U := (baseChange f).obj T
  let hU : IsTerminal U := IsTerminal.isTerminalObj (baseChange f) T hT
  let ao := constantSheafAdj (J Y) A hT
  let bo := constantSheafAdj (J X) A hU
  let c := ao.comp ad
  apply (c.homEquiv (B M) (functions M X)).injective
  have h₁ : c.homEquiv (B M) (functions M X) (L.map (constantIso Y M).hom ≫ a M f) =
      (constantToContinuous Y M).app (op T) ≫ (diagonal M f).hom.app (op T) := by
    change (ao.homEquiv (B M) (R.obj (functions M X)))
      ((ad.homEquiv (C M Y) (functions M X)) (L.map (constantIso Y M).hom ≫ a M f)) = _
    rw [ad.homEquiv_naturality_left]
    rw [show (ad.homEquiv (functions M Y) (functions M X)) (a M f) = diagonal M f from
      (ad.homEquiv _ _).apply_symm_apply _]
    rw [ao.homEquiv_naturality_right, evaluate_constant M hT] <;> rfl
  have h₂ : c.homEquiv (B M) (functions M X)
      (((constantInverseImageIso f).app (B M)).hom ≫ (constantIso X M).hom) =
      (constantToContinuous X M).app (op U) := by
    change (c.homEquiv (B M) (functions M X)) ((c.leftAdjointUniq bo).hom.app (B M) ≫
      (constantIso X M).hom) = _
    rw [c.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change bo.unit.app (B M) ≫ ((sheafSections (J X) A).obj (op U)).map (constantIso X M).hom = _
    exact (bo.homEquiv_unit (B M) (functions M X) (constantIso X M).hom).symm.trans
      (evaluate_constant M hU)
  exact h₁.trans ((diagonal_label M f T).trans h₂.symm)

set_option maxHeartbeats 6400000 in
/-- The continuous and constant native pullbacks agree in every degree for discrete coefficients. -/
theorem cohomology_pullback (n : ℕ) (z : Sheaf.H (C M Y) n) :
    continuous f M n (Sheaf.H.map (constantIso Y M).hom n z) =
      Sheaf.H.map (constantIso X M).hom n (constant f (B M) n z) := by
  let q := pullback f (C M Y) n z
  change Sheaf.H.map (a M f) n (pullback f (functions M Y) n
      (Sheaf.H.map (constantIso Y M).hom n z)) =
    Sheaf.H.map (constantIso X M).hom n
      (Sheaf.H.map ((constantInverseImageIso f).app (B M)).hom n q)
  have hpb := pullback_naturality f (constantIso Y M).hom n z
  refine (congrArg (fun k ↦ Sheaf.H.map (a M f) n k) hpb).trans ?_
  let g := (inverseImage f).map (constantIso Y M).hom
  let b := ((constantInverseImageIso f).app (B M)).hom
  let j := (constantIso X M).hom
  exact (Sheaf.H.map_comp_apply (f := g) (n := n) (a M f) q).symm.trans
    ((congrArg (fun t ↦ Sheaf.H.map t n q) (coefficient_pullback M f)).trans
      (Sheaf.H.map_comp_apply (f := b) (n := n) j q))

end
end ManuscriptAudit.ProetaleDiscreteSchemePullback

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleDiscreteSchemePullback.cohomology_pullback
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
