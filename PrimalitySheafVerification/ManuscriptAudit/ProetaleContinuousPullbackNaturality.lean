import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback

/-! Actual continuous pro-étale coefficient pullback commutes with
postcomposition by the coefficient homomorphism. -/

namespace ManuscriptAudit.ProetaleContinuousPullbackNaturality

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleBaseChange (directImage)
open ProetaleInverseImage (inverseImage adjunction)
open ProetaleSchemeCohomologyPullback (pullback pullback_naturality mapOfDirectImage continuous)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleResidueSheaves (coefficientMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

set_option maxHeartbeats 4900000 in
/-- The actual direct-image description computes naturality in both coefficients. -/
theorem mapOfDirectImage_natural {F F' : P Y} {E E' : P X}
    (a : F ⟶ (directImage f A).obj E) (a' : F' ⟶ (directImage f A).obj E')
    (g : F ⟶ F') (h : E ⟶ E') (w : g ≫ a' = a ≫ (directImage f A).map h)
    (n : ℕ) (x : Sheaf.H F n) :
    mapOfDirectImage f a' n (Sheaf.H.map g n x) =
      Sheaf.H.map h n (mapOfDirectImage f a n x) := by
  let ad := adjunction f
  let b := (ad.homEquiv F E).symm a
  let b' := (ad.homEquiv F' E').symm a'
  have hw : (inverseImage f).map g ≫ b' = b ≫ h := by
    rw [← ad.homEquiv_naturality_left_symm, ← ad.homEquiv_naturality_right_symm, w]
  let z := pullback f F n x
  change Sheaf.H.map b' n (pullback f F' n (Sheaf.H.map g n x)) =
    Sheaf.H.map h n (Sheaf.H.map b n z)
  have hpb := pullback_naturality f g n x
  refine (congrArg (fun c ↦ Sheaf.H.map b' n c) hpb).trans ?_
  exact (Sheaf.H.map_comp_apply (f := (inverseImage f).map g) (n := n) b' z).symm.trans
    ((congrArg (fun t ↦ Sheaf.H.map t n z) hw).trans
      (Sheaf.H.map_comp_apply (f := b) (n := n) h z))

variable {M N : Type} [AddCommGroup M] [AddCommGroup N] [TopologicalSpace M] [TopologicalSpace N]
    [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]
  (q : M →+ N) (hq : Continuous q)

/-- The actual lifted map of continuous coefficient sheaves. -/
abbrev coeff (Z : Scheme.{0}) : functions M Z ⟶ functions N Z :=
  (sheafCompose (Scheme.ProEt.topology Z) AddCommGrpCat.uliftFunctor.{1}).map (coefficientMap Z q hq)

set_option maxHeartbeats 4200000 in
theorem diagonal_natural :
    coeff q hq Y ≫ diagonal N f = diagonal M f ≫ (directImage f A).map (coeff q hq X) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

/-- Continuous coefficient reduction and actual scheme pullback commute in every degree. -/
theorem continuous_natural (n : ℕ) (x : Sheaf.H (functions M Y) n) :
    continuous f N n (Sheaf.H.map (coeff q hq Y) n x) =
      Sheaf.H.map (coeff q hq X) n (continuous f M n x) :=
  mapOfDirectImage_natural f (diagonal M f) (diagonal N f) (coeff q hq Y) (coeff q hq X)
    (diagonal_natural f q hq) n x

end
end ManuscriptAudit.ProetaleContinuousPullbackNaturality

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleContinuousPullbackNaturality.continuous_natural
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
