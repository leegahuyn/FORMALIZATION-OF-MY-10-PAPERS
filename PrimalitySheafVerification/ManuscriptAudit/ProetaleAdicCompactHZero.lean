import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenCounitMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointClosedSupport
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueHomeomorphism
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal

/-! The native extension by zero of the genuine continuous adic coefficients
has zero global sections on a preconnected ambient scheme when the open
omits a closed rational point. -/

namespace ManuscriptAudit.ProetaleAdicCompactHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenProetaleExtension (extensionByZero restriction abelianExtensionByZeroAdjunction)
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedKernelLocalSupport (K inc)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleOpenCounitMono (extensionRestrictionMap extensionRestrictionMap_mono)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (L : Type) [Field L] (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

theorem continuous_value_eq {V : Type} [TopologicalSpace V] [PreconnectedSpace V]
    (f : C(V, M ℓ)) (x y : V) : f x = f y := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  let r := (PadicInt.toZModPow n : M ℓ → ZMod (ℓ ^ n))
  exact TotallyDisconnectedSpace.eq_of_continuous (r ∘ f)
    ((PadicResidueHomeomorphism.reduction_continuous ℓ n).comp f.continuous) x y

private def restrictionSupportIso (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    (restriction j A).obj (K i (M ℓ)) ≅ functions (M ℓ) U := by
  let R := restriction j A
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  have h : R.map (diagonal (M ℓ) i) = 0 :=
    (ProetaleDisjointClosedSupport.restriction_closed_isZero i j (M ℓ) hDisjoint).eq_of_tgt _ _
  letI := kernel.ι_of_zero h
  exact PreservesKernel.iso R (diagonal (M ℓ) i) ≪≫ asIso (kernel.ι (R.map (diagonal (M ℓ) i))) ≪≫
    restrictionFunctionsIso j (M ℓ)

/-- A genuinely supported continuous section vanishes on the omitted boundary,
and extension by zero maps monomorphically to that support kernel. -/
def supportMap (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    (extensionByZero j A).obj (functions (M ℓ) U) ⟶ K i (M ℓ) :=
  ((extensionByZero j A).mapIso (restrictionSupportIso ℓ j L i hDisjoint)).inv ≫
    extensionRestrictionMap j (K i (M ℓ))

theorem supportMap_mono (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    Mono (supportMap ℓ j L i hDisjoint) := by
  letI := extensionRestrictionMap_mono j (K i (M ℓ))
  rw [supportMap]
  infer_instance

variable [PreconnectedSpace X]

theorem restriction_HZero_injective : Function.Injective (Sheaf.H.map (diagonal (M ℓ) i) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let e := Sheaf.H.equiv₀ (functions (M ℓ) X) hT
  intro a b hab
  apply e.injective
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  let z : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
  obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := 𝟙 X) (g := i) (i z) z rfl
  have h := congrArg (Sheaf.H.equiv₀ (functionsOver (M ℓ) i) hT) hab
  simp only [← Sheaf.H.equiv₀_naturality] at h
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback (𝟙 X) i : Scheme.{0}), M ℓ)) ↦ f.down q) h
  let a' : C(X, M ℓ) := (e a).down
  let b' : C(X, M ℓ) := (e b).down
  change a' (pullback.fst (𝟙 X) i q) = b' (pullback.fst (𝟙 X) i q) at h'
  rw [hq] at h'
  exact (continuous_value_eq ℓ a' x (i z)).trans
    (h'.trans (continuous_value_eq ℓ b' (i z) x))

private theorem kernelHZero_subsingleton : Subsingleton (Sheaf.H (K i (M ℓ)) 0) := by
  let T := (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  have hi : Function.Injective (Sheaf.H.map (inc i (M ℓ)) 0) :=
    Ext.postcomp_mk₀_injective_of_mono T (inc i (M ℓ))
  refine ⟨fun a b ↦ hi (restriction_HZero_injective ℓ L i ?_)⟩
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, kernel.condition]
  simp only [Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

/-- Native compact degree zero of continuous adic coefficients vanishes
for an open missing the displayed field-valued closed point. -/
theorem compactHZero_subsingleton (hDisjoint : Disjoint (Set.range j) (Set.range i)) :
    Subsingleton (Sheaf.H ((extensionByZero j A).obj (functions (M ℓ) U)) 0) := by
  let B := supportMap ℓ j L i hDisjoint
  letI : Mono B := supportMap_mono ℓ j L i hDisjoint
  letI := kernelHZero_subsingleton ℓ L i
  let T := (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  have hB : Function.Injective (Sheaf.H.map B 0) :=
    Ext.postcomp_mk₀_injective_of_mono T B
  exact hB.subsingleton

end

end ManuscriptAudit.ProetaleAdicCompactHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicCompactHZero.supportMap_mono,
      ``ManuscriptAudit.ProetaleAdicCompactHZero.restriction_HZero_injective,
      ``ManuscriptAudit.ProetaleAdicCompactHZero.compactHZero_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
