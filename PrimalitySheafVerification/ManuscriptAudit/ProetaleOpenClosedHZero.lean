import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHOne

/-! The native extension by zero of discrete coefficients has no
global sections when a preconnected ambient scheme omits a rational point. -/

namespace ManuscriptAudit.ProetaleOpenClosedHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (finalObject)
open ProetaleClosedKernelLocalSupport (K inc)
open ProetaleClosedOpenRestriction (extensionFunctionsIsoKernel)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} [PreconnectedSpace X]
variable (L : Type) [Field L] (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}

theorem restriction_HZero_injective : Function.Injective (Sheaf.H.map (diagonal M i) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let e := Sheaf.H.equiv₀ (functions M X) hT
  intro a b hab
  apply e.injective
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  let z : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
  obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := 𝟙 X) (g := i) (i z) z rfl
  have h := congrArg (Sheaf.H.equiv₀ (functionsOver M i) hT) hab
  simp only [← Sheaf.H.equiv₀_naturality] at h
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback (𝟙 X) i : Scheme.{0}), M)) ↦ f.down q) h
  let a' : C(X, M) := (e a).down
  let b' : C(X, M) := (e b).down
  change a' (pullback.fst (𝟙 X) i q) = b' (pullback.fst (𝟙 X) i q) at h'
  rw [hq] at h'
  exact (TotallyDisconnectedSpace.eq_of_continuous a' a'.continuous x (i z)).trans
    (h'.trans (TotallyDisconnectedSpace.eq_of_continuous b' b'.continuous (i z) x))

theorem kernelHZero_subsingleton : Subsingleton (Sheaf.H (K i M) 0) := by
  let T := (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  have hi : Function.Injective (Sheaf.H.map (inc i M) 0) :=
    Ext.postcomp_mk₀_injective_of_mono T (inc i M)
  refine ⟨fun a b ↦ hi (restriction_HZero_injective L i M ?_)⟩
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, kernel.condition]
  simp only [Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

/-- Native compact degree zero vanishes for a complementary open of a preconnected ambient scheme. -/
theorem compactFunctionsHZero_subsingleton {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]
    (complement : Set.range j = (Set.range i)ᶜ) :
    Subsingleton (Sheaf.H ((extensionByZero j A).obj (functions M Y)) 0) := by
  letI := kernelHZero_subsingleton L i M
  exact (cohomologyIso (X := X) (extensionFunctionsIsoKernel i j M complement) 0).injective.subsingleton

end
end ManuscriptAudit.ProetaleOpenClosedHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenClosedHZero.restriction_HZero_injective,
      ``ManuscriptAudit.ProetaleOpenClosedHZero.kernelHZero_subsingleton,
      ``ManuscriptAudit.ProetaleOpenClosedHZero.compactFunctionsHZero_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
