import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicScalarAction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHOneDetection
import PrimalitySheafVerification.ManuscriptAudit.PadicPowerContinuousExact
import PrimalitySheafVerification.ManuscriptAudit.PointwiseSheafShortExact
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionExact

/-! The genuine continuous adic coefficient sheaf has the actual multiplication
and residue short exact sequence, also after native extension by zero. -/

namespace ManuscriptAudit.ProetaleAdicPowerSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleAdicHOneDetection (finiteCoefficient)
open NativeAdicScalarAction (scalarMap)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev F := functions ℤ_[ℓ] X

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

abbrev multiply : F X ℓ ⟶ F X ℓ := scalarMap X ℓ ((ℓ : ℤ_[ℓ]) ^ r)

abbrev residue : F X ℓ ⟶ finiteCoefficient X ℓ r :=
  (ProetaleCoefficientUniverseLift.lift X).map (ProetaleResidueSheaves.residueReduction X ℓ r)

private theorem cast_reduces_zero : PadicInt.toZModPow r ((ℓ : ℤ_[ℓ]) ^ r) = 0 := by
  rw [← Nat.cast_pow, map_natCast, ZMod.natCast_self]

private theorem comp_zero : multiply X ℓ r ≫ residue X ℓ r = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro f
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change PadicInt.toZModPow r (((ℓ : ℤ_[ℓ]) ^ r) *
    (show C(W.unop.left, ℤ_[ℓ]) from f.down) x) = 0
  rw [map_mul, cast_reduces_zero ℓ r, zero_mul]

/-- Actual multiplication by the adic prime power followed by the actual finite residue. -/
def sequence : ShortComplex (Sheaf (J X) A) :=
  ShortComplex.mk (multiply X ℓ r) (residue X ℓ r) (comp_zero X ℓ r)

private abbrev eval (W : X.ProEtᵒᵖ) :=
  sheafToPresheaf (J X) A ⋙ (evaluation X.ProEtᵒᵖ A).obj W

set_option maxHeartbeats 1800000 in
private theorem evaluated_shortExact (W : X.ProEtᵒᵖ) :
    ((sequence X ℓ r).map (eval X W)).ShortExact := by
  let S := (sequence X ℓ r).map (eval X W)
  let V := W.unop.left
  have hm : Mono S.f := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro a b h
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact PadicPowerContinuousExact.mulPower_injective ℓ r
      (congrArg (fun y : ULift.{1} (C(↥V, ℤ_[ℓ])) ↦ y.down x) h)
  have he : Epi S.g := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨f, hf⟩ := PadicPowerContinuousExact.exists_residue_lift ℓ r s.down
    refine ⟨⟨f⟩, ?_⟩
    apply ULift.ext
    exact ContinuousMap.ext hf
  refine ShortComplex.ShortExact.mk' ?_ hm he
  rw [ShortComplex.ab_exact_iff_function_exact]
  intro s
  constructor
  · intro hs
    have hs' (x : V) : PadicInt.toZModPow r ((show C(↥V, ℤ_[ℓ]) from s.down) x) = 0 :=
      congrArg (fun y : ULift.{1} (C(↥V, ZMod (ℓ ^ r))) ↦ y.down x) hs
    obtain ⟨f, hf⟩ := PadicPowerContinuousExact.exists_division ℓ r s.down hs'
    refine ⟨⟨f⟩, ?_⟩
    apply ULift.ext
    exact ContinuousMap.ext hf
  · rintro ⟨a, rfl⟩
    exact ConcreteCategory.congr_hom S.zero a

/-- The actual residue of native coefficients is the cokernel
of multiplication by the corresponding power of the adic prime. -/
theorem sequence_shortExact : (sequence X ℓ r).ShortExact :=
  PointwiseSheafShortExact.shortExact (J X) (sequence X ℓ r) (evaluated_shortExact X ℓ r)

variable {U Y : Scheme.{0}} (j : U ⟶ Y) [IsOpenImmersion j]

local instance extensionAdditive : (extensionByZero j A).Additive := by
  letI := ProetaleOpenExtensionExact.extensionByZero_preservesFiniteLimits j
  exact (extensionByZero j A).additive_of_preserves_binary_products

abbrev compactSequence := (sequence U ℓ r).map (extensionByZero j A)

/-- The very same short exact sequence after genuine pro-étale extension by zero. -/
theorem compactSequence_shortExact : (compactSequence ℓ r j).ShortExact := by
  let E := extensionByZero j A
  letI : PreservesFiniteLimits E := ProetaleOpenExtensionExact.extensionByZero_preservesFiniteLimits j
  letI : PreservesFiniteColimits E := ProetaleOpenExtensionExact.extensionByZero_preservesFiniteColimits j
  letI : E.Additive := E.additive_of_preserves_binary_products
  exact (sequence_shortExact U ℓ r).map_of_exact E

end

end ManuscriptAudit.ProetaleAdicPowerSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicPowerSequence.sequence_shortExact,
      ``ManuscriptAudit.ProetaleAdicPowerSequence.compactSequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
