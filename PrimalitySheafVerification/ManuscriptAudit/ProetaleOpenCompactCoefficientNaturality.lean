import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenContinuousPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteConstant

/-! Pullback with compact support along an actual cartesian square of opens
commutes with a continuous coefficient map. The same construction on a
discrete coefficient gives pullback on extension by zero of the constant sheaf. -/

namespace ManuscriptAudit.ProetaleOpenCompactCoefficientNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleContinuousPullbackNaturality (coeff diagonal_natural mapOfDirectImage_natural)
open ProetaleDirectImageRestrictionPullback (directImageRestrictionIso)
open ProetaleOpenContinuousPullback (compactToDirectImage compactMap)
open ProetaleSchemeCohomologyPullback (mapOfDirectImage)
open OpenProetaleExtension (extensionByZero restriction abelianExtensionByZeroAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

variable {X Y V U : Scheme.{0}}
  (f : X ⟶ Y) (g : V ⟶ U) (i : V ⟶ X) (j : U ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (H : IsPullback i g f j)

variable {M N : Type} [AddCommGroup M] [AddCommGroup N] [TopologicalSpace M]
  [TopologicalSpace N] [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
  (q : M →+ N) (hq : Continuous q)

set_option maxHeartbeats 7100000 in
theorem directImage_natural :
    (extensionByZero j A).map (coeff q hq U) ≫ compactToDirectImage f g i j H N =
      compactToDirectImage f g i j H M ≫
        (directImage f A).map ((extensionByZero i A).map (coeff q hq V)) := by
  let a := abelianExtensionByZeroAdjunction j
  let b := abelianExtensionByZeroAdjunction i
  let Q := directImage g A
  let R := directImage f A ⋙ restriction j A
  let S := restriction i A ⋙ Q
  let e : R ≅ S := directImageRestrictionIso H
  let T := (extensionByZero i A).obj (functions M V)
  let T' := (extensionByZero i A).obj (functions N V)
  let z : T ⟶ T' := (extensionByZero i A).map (coeff q hq V)
  let aU := coeff q hq U
  let aV := coeff q hq V
  let u := b.unit.app (functions M V)
  let u' := b.unit.app (functions N V)
  let d := diagonal M g
  let d' := diagonal N g
  apply (a.homEquiv (functions M U) ((directImage f A).obj T')).injective
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
  change aU ≫ (a.homEquiv _ _) ((a.homEquiv _ _).symm (d' ≫ Q.map u' ≫ e.inv.app T')) =
    (a.homEquiv _ _) ((a.homEquiv _ _).symm (d ≫ Q.map u ≫ e.inv.app T)) ≫ R.map z
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hd : aU ≫ d' = d ≫ Q.map aV := diagonal_natural g q hq
  have hu : aV ≫ u' = u ≫ (restriction i A).map z := b.unit.naturality aV
  have he : e.inv.app T ≫ R.map z = Q.map ((restriction i A).map z) ≫ e.inv.app T' :=
    (e.inv.naturality z).symm
  calc
    aU ≫ d' ≫ Q.map u' ≫ e.inv.app T' =
        (aU ≫ d') ≫ Q.map u' ≫ e.inv.app T' := by simp only [Category.assoc]
    _ = d ≫ Q.map (aV ≫ u') ≫ e.inv.app T' := by rw [hd, Q.map_comp]; simp only [Category.assoc]
    _ = (d ≫ Q.map u ≫ e.inv.app T) ≫ R.map z := by
      rw [hu, Q.map_comp]
      simp only [Category.assoc, he]

/-- Coefficient reduction commutes with genuine pullback in all compact-support degrees. -/
theorem compact_natural (n : ℕ)
    (x : Sheaf.H ((extensionByZero j A).obj (functions M U)) n) :
    compactMap f g i j H N n (Sheaf.H.map ((extensionByZero j A).map (coeff q hq U)) n x) =
      Sheaf.H.map ((extensionByZero i A).map (coeff q hq V)) n (compactMap f g i j H M n x) :=
  mapOfDirectImage_natural f (compactToDirectImage f g i j H M) (compactToDirectImage f g i j H N)
    ((extensionByZero j A).map (coeff q hq U)) ((extensionByZero i A).map (coeff q hq V))
    (directImage_natural f g i j H q hq) n x

variable (M) [DiscreteTopology M]

/-- The actual extension-by-zero comparison for discrete coefficients. -/
def discreteIso {U Y : Scheme.{0}} (j : U ⟶ Y) [IsOpenImmersion j] :
    (extensionByZero j A).obj (ProetaleConstantRestriction.constant U M) ≅
      (extensionByZero j A).obj (functions M U) :=
  (extensionByZero j A).mapIso (ProetaleDiscreteConstant.constantIso U M)

/-- The genuine compact-support pullback on the constant sheaf of a discrete group. -/
def discreteMap (n : ℕ) :
    Sheaf.H ((extensionByZero j A).obj (ProetaleConstantRestriction.constant U M)) n →+
      Sheaf.H ((extensionByZero i A).obj (ProetaleConstantRestriction.constant V M)) n :=
  mapOfDirectImage f ((discreteIso M j).hom ≫ compactToDirectImage f g i j H M ≫
    (directImage f A).map (discreteIso M i).inv) n

set_option maxHeartbeats 6500000 in
theorem discrete_cohomology_comparison (n : ℕ)
    (x : Sheaf.H ((extensionByZero j A).obj (ProetaleConstantRestriction.constant U M)) n) :
    compactMap f g i j H M n (Sheaf.H.map (discreteIso M j).hom n x) =
      Sheaf.H.map (discreteIso M i).hom n (discreteMap f g i j H M n x) := by
  let d := compactToDirectImage f g i j H M
  let D := directImage f A
  let e := discreteIso M j
  let e' := discreteIso M i
  have h : e.hom ≫ d = (e.hom ≫ d ≫ D.map e'.inv) ≫ D.map e'.hom := by
    simp only [Category.assoc]
    rw [← D.map_comp, e'.inv_hom_id, D.map_id, Category.comp_id]
  exact mapOfDirectImage_natural f (e.hom ≫ d ≫ D.map e'.inv) d e.hom e'.hom h n x

end
end ManuscriptAudit.ProetaleOpenCompactCoefficientNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleOpenCompactCoefficientNaturality.compact_natural,
      ``ManuscriptAudit.ProetaleOpenCompactCoefficientNaturality.discrete_cohomology_comparison] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
