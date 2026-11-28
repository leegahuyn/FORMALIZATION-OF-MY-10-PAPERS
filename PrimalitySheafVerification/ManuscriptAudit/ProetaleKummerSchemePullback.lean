import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerKernelTransition

/-! The actual units and categorical Kummer kernels pull back along scheme maps. -/

namespace ManuscriptAudit.ProetaleKummerSchemePullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleInverseImage (inverseImage adjunction)
open ProetaleUnitSheaf (underlying unitSheaf)
open ProetaleKummerPower (power)
open ProetaleKummerSequence (sequence sequence_shortExact)
open ProetaleKummerKernelTransition (kernelBoundary)
open ProetaleSchemeCohomologyPullback (pullback pullback_boundary)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private def chartProjection : baseChange f ⋙ underlying X ⟶ underlying Y where
  app W := pullback.fst W.hom f
  naturality := by
    intro U V g
    change ((baseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

/-- Maps of actual coordinate units via the projection from each base-changed chart. -/
def unitsToDirectImage : unitSheaf Y ⟶ (directImage f A).obj (unitSheaf X) :=
  ⟨Functor.whiskerRight (chartProjection f).op
    (Scheme.Γ ⋙ ringUnits ⋙ AddCommGrpCat.uliftFunctor.{1})⟩

/-- The native units inverse-image map is induced by pullback of ordinary units. -/
def unitsPullback : (inverseImage f).obj (unitSheaf Y) ⟶ unitSheaf X :=
  ((adjunction f).homEquiv _ _).symm (unitsToDirectImage f)

private theorem power_commutes (d : ℕ) :
    unitsPullback f ≫ power X d = (inverseImage f).map (power Y d) ≫ unitsPullback f := by
  simp only [power, Functor.map_nsmul, Functor.map_id, Preadditive.comp_nsmul,
    Preadditive.nsmul_comp, Category.id_comp, Category.comp_id]

/-- The natural inverse-image map on the actual kernel of the power map. -/
def kernelPullback (d : ℕ) :
    (inverseImage f).obj (kernel (power Y d)) ⟶ kernel (power X d) :=
  kernel.lift (power X d) ((inverseImage f).map (kernel.ι (power Y d)) ≫ unitsPullback f) (by
    rw [Category.assoc, power_commutes, ← Category.assoc, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp])

/-- The morphism of actual Kummer short complexes. -/
def sequencePullback (d : ℕ) : (sequence Y d).map (inverseImage f) ⟶ sequence X d where
  τ₁ := kernelPullback f d
  τ₂ := unitsPullback f
  τ₃ := unitsPullback f
  comm₁₂ := kernel.lift_ι _ _ _
  comm₂₃ := power_commutes f d

/-- Native cohomological pullback for the actual units sheaf. -/
def unitsMap (n : ℕ) : Sheaf.H (unitSheaf Y) n →+ Sheaf.H (unitSheaf X) n :=
  (Sheaf.H.map (unitsPullback f) n).comp (pullback f (unitSheaf Y) n)

/-- Native cohomological pullback for the literal Kummer kernel. -/
def kernelMap (d n : ℕ) :
    Sheaf.H (kernel (power Y d)) n →+ Sheaf.H (kernel (power X d)) n :=
  (Sheaf.H.map (kernelPullback f d) n).comp (pullback f (kernel (power Y d)) n)

variable {K : Type} [Field K]
  (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
  (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

/-- The actual Kummer boundary commutes with pullback of each global unit. -/
theorem kernelBoundary_natural (u : Sheaf.H (unitSheaf Y) 0) :
    kernelMap f d 1 (kernelBoundary y d u) = kernelBoundary x d (unitsMap f 0 u) := by
  let h := sequence_shortExact y d
  let h' := sequence_shortExact x d
  let hL := h.map_of_exact (inverseImage f)
  have ht := hL.extClass_naturality h' (sequencePullback f d)
  change hL.extClass.comp (Ext.mk₀ (kernelPullback f d)) rfl =
    (Ext.mk₀ (unitsPullback f)).comp h'.extClass rfl at ht
  let v := pullback f (unitSheaf Y) 0 u
  have hu := pullback_boundary f h 0 u
  change pullback f (kernel (power Y d)) 1 (u.comp h.extClass rfl) = v.comp hL.extClass rfl at hu
  change (pullback f (kernel (power Y d)) 1 (u.comp h.extClass rfl)).comp
    (Ext.mk₀ (kernelPullback f d)) rfl = (v.comp (Ext.mk₀ (unitsPullback f)) rfl).comp h'.extClass rfl
  rw [hu, Ext.comp_assoc_of_third_deg_zero, ht, Ext.comp_assoc_of_second_deg_zero]

end
end ManuscriptAudit.ProetaleKummerSchemePullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleKummerSchemePullback.unitsToDirectImage,
      ``ManuscriptAudit.ProetaleKummerSchemePullback.sequencePullback,
      ``ManuscriptAudit.ProetaleKummerSchemePullback.kernelBoundary_natural] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
